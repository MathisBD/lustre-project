open Asttypes
open Typed_ast
open Delay_types

(** Exception raised when a node is not properly initialized. *)
exception Initialization

(** Maps over strings. *)
module StringMap = Map.Make (String)

(** [mk_d_tuple [d_1; d_2; ...]] makes the delay type [(d_1, d_2, ...)].
    @raise Invalid_argument if a [d_i] is a function type. *)
let mk_d_tuple (ds : d_type list) : d_type =
  let raw_ds =
    List.map (function Dprod d -> d | _ -> raise @@ Invalid_argument "mk_d_tuple") ds
  in
  Dprod (Dtuple raw_ds)

(**************************************************************************)
(** *** Delay Subtyping. *)
(**************************************************************************)

(** The delay environment associates to each variable identifier a thunk which returns :
    - a fresh delay type.
    - a set of constraints on the delay variables occuring in the above type.

    We use a thunk so that accessing the delay type of a variable always returns a new
    instantiation of the delay type and constraints. *)
type d_env = (unit -> d_type * Constraints.t) StringMap.t

(** TODO : replace SubtypingErrpr by Initialization. *)

(** [SubtypingError (cs, t1, t2)] means that we could not add the subtyping constraint
    [t1 <= t2] in constraint set [cs]. *)
exception SubtypingError of Constraints.t * d_type * d_type

(** [fresh_delay_var ()] generates a fresh delay variable. *)
let fresh_delay_var : unit -> d_atom =
  let counter = ref 0 in
  fun () ->
    counter := !counter + 1;
    Dvar !counter

(** Compute subtyping constraints on [d_atom].
    @raise SubtypingError *)
let d_atom_subtyping (cs : Constraints.t) (d1 : d_atom) (d2 : d_atom) : Constraints.t =
  match (d1, d2) with
  (* Trivial constraints : as an optimization, we don't add any constraint to the graph. *)
  | D0, _ | _, D1 -> cs
  (* Non-trivial constraints : add an edge to the graph and check it is still consistent. *)
  | _, _ ->
      let cs' = Constraints.add cs d1 d2 in
      if Constraints.consistent cs'
      then cs'
      else raise @@ SubtypingError (cs, Dprod (Datom d1), Dprod (Datom d2))

(** Compute subtyping constraints on [d_prod].
    @raise SubtypingError *)
let rec d_prod_subtyping (cs : Constraints.t) (d1 : d_prod) (d2 : d_prod) : Constraints.t
    =
  match (d1, d2) with
  | Datom d1, Datom d2 -> d_atom_subtyping cs d1 d2
  | Dtuple d1s, Dtuple d2s when List.length d1s = List.length d2s ->
      List.fold_left2 d_prod_subtyping cs d1s d2s
  | _, _ -> raise @@ SubtypingError (cs, Dprod d1, Dprod d2)

(** Compute subtyping constraints on [d_type].
    @raise SubtypingError *)
let d_type_subtyping (cs : Constraints.t) (d1 : d_type) (d2 : d_type) : Constraints.t =
  match (d1, d2) with
  | Dfunc (d1, d1'), Dfunc (d2, d2') ->
      (* Functions are contravariant in the argument and covariant in the result. *)
      let cs = d_prod_subtyping cs d2 d1 in
      d_prod_subtyping cs d1' d2'
  | Dprod d1, Dprod d2 -> d_prod_subtyping cs d1 d2
  | _, _ -> raise @@ SubtypingError (cs, d1, d2)

(**************************************************************************)
(** *** Delay Inference. *)
(**************************************************************************)

(** [infer_unop cs op] returns a freshly instantiated delay type for unary operator [op].
*)
let infer_unop (cs : Constraints.t) (op : unop) : d_type * Constraints.t =
  match op with
  | Unot | Uminus | Uminus_f ->
      (* All unary operators we support have type [forall d. d -> d]. *)
      let dvar = Datom (fresh_delay_var ()) in
      (Dfunc (dvar, dvar), cs)

(** [infer_binop cs op] returns a freshly instantiated delay type for binary operator
    [op]. *)
let infer_binop (cs : Constraints.t) (op : binop) : d_type * Constraints.t =
  match op with
  | Beq | Bneq | Blt | Ble | Bgt | Bge | Badd | Bsub | Bmul | Badd_f | Bsub_f | Bmul_f
  | Band | Bor ->
      (* Most binary operators we support have type [forall d. d * d -> d]. *)
      let dvar = fresh_delay_var () in
      (Dfunc (Dtuple [ Datom dvar; Datom dvar ], Datom dvar), cs)
  | Bdiv | Bmod | Bdiv_f ->
      (* Division and related operators have type [forall d. d * 0 -> d]. *)
      let dvar = fresh_delay_var () in
      (Dfunc (Dtuple [ Datom dvar; Datom D0 ], Datom dvar), cs)

(** Infer a [d_type] for a function application, accumulating subtyping constraints.
    @raise SubtypingError
      if the actual argument type is not a subtype of the function's expected argument
      type. *)
let infer_app (cs : Constraints.t) (d_f : d_type) (d_arg : d_type) :
    d_type * Constraints.t =
  match d_f with
  | Dprod _ -> failwith "d_type_app : expected a function type"
  | Dfunc (d_f_arg, d_f_res) -> (Dprod d_f_res, d_type_subtyping cs d_arg (Dprod d_f_arg))

(** Infer a [d_type] for a variable or node by looking it up in the delay environment. *)
let infer_ident (env : d_env) (cs : Constraints.t) (x : string) : d_type * Constraints.t =
  (* Lookup the identifier in the delay environment. *)
  match StringMap.find_opt x env with
  | Some thunk ->
      (* Compute a fresh instantiation of the delay type and constraints. *)
      let d_x, cs_x = thunk () in
      (* Accumulate the new constraints. *)
      let cs =
        List.fold_left
          (fun cs (d1, d2) -> Constraints.add cs d1 d2)
          cs (Constraints.to_list cs_x)
      in
      (d_x, cs)
  | None -> failwith "infer_ident : unbound identifier"

(** [infer_expr env cs e] infers a delay type for expression [e] in delay environment
    [env] and with constraints [cs].
    @raise SubtypingError *)
let rec infer_expr (env : d_env) (cs : Constraints.t) (e : t_expr) :
    d_type * Constraints.t =
  let res, cs =
    match e.texpr_desc with
    | TE_const _ ->
        (* Constants are always initialized. *)
        (Dprod (Datom D0), cs)
    | TE_ident x -> infer_ident env cs x
    | TE_unop (op, e) ->
        let d_op, cs = infer_unop cs op in
        let d_e, cs = infer_expr env cs e in
        infer_app cs d_op d_e
    | TE_binop (op, e1, e2) ->
        let d_op, cs = infer_binop cs op in
        let d_args, cs = infer_tuple env cs [ e1; e2 ] in
        infer_app cs d_op d_args
    | TE_app (f, es) ->
        let d_f, cs = infer_ident env cs f in
        let d_es, cs = infer_tuple env cs es in
        infer_app cs d_f d_es
    | TE_prim (_f, _es) -> failwith "infer_expr : TE_prim not implemented yet"
    | TE_if (e1, e2, e3) ->
        (* [if-then-else] has type [forall d. d * d * d -> d]. *)
        let dvar = Datom (fresh_delay_var ()) in
        let d_if = Dfunc (Dtuple [ dvar; dvar; dvar ], dvar) in
        let d_args, cs = infer_tuple env cs [ e1; e2; e3 ] in
        infer_app cs d_if d_args
    | TE_pre e ->
        (* [pre] has type [0 -> 1]. *)
        let d_pre = Dfunc (Datom D0, Datom D1) in
        let d_e, cs = infer_expr env cs e in
        infer_app cs d_pre d_e
    | TE_arrow (e1, e2) ->
        (* [->] has type [forall d. d * 1 -> d]. *)
        let dvar = Datom (fresh_delay_var ()) in
        let d_arrow = Dfunc (Dtuple [ dvar; Datom D1 ], dvar) in
        let d_args, cs = infer_tuple env cs [ e1; e2 ] in
        infer_app cs d_arrow d_args
    | TE_tuple es -> infer_tuple env cs es
    | TE_print es ->
        (* The printing function has type [forall d. (d * d * ...) -> d]. *)
        let dvar = Datom (fresh_delay_var ()) in
        let d_print = Dfunc (Dtuple (List.map (fun _ -> dvar) es), dvar) in
        let d_args, cs = infer_tuple env cs es in
        infer_app cs d_print d_args
  in
  Format.printf "INFER %a |- %a : %a@\n" Constraints.print cs Typed_ast_printer.print_exp
    e print_d_type res;
  (res, cs)

(** Helper function to infer a [d_type] for a tuple of expressions, and assemble the
    resulting delays in a tuple. It assumes there are at least two expressions (i.e. it
    always returns a [Dtuple]).
    @raise SubtypingError *)
and infer_tuple (env : d_env) (cs : Constraints.t) (es : t_expr list) :
    d_type * Constraints.t =
  let rec loop cs = function
    | [] -> ([], cs)
    | e :: es ->
        let d_e, cs = infer_expr env cs e in
        let d_es, cs = loop cs es in
        (d_e :: d_es, cs)
  in
  let d_es, cs = loop cs es in
  (mk_d_tuple d_es, cs)

(** Infer a delay type for each variable bound by an equation. *)
let infer_equation (env : d_env) (cs : Constraints.t) (eq : t_equation) :
    (string * d_prod) list * Constraints.t =
  let d_eq, cs = infer_expr env cs eq.teq_expr in
  match (eq.teq_patt.tpatt_desc, d_eq) with
  | [ v ], Dprod d -> ([ (v, d) ], cs)
  | vs, Dprod (Dtuple ds) when List.length ds = List.length vs -> (List.combine vs ds, cs)
  | _ -> failwith "infer_equation : invalid pattern"

(** Check a node is well initialized in a given delay environment, and add the node to the
    delay environment. This assumes the node has already been scheduled.
    @raise Initialization if the node is not properly initialized. *)
let check_node (env : d_env) (node : t_node) : d_env =
  Format.printf "NODE %s\n" node.tn_name;
  (* Add the node's inputs to the delay environment. 
     Careful : the delay types of the inputs are fixed (i.e. not polymorphic), and must _not_
     be refreshed each time they are accessed. *)
  let d_inputs = List.map (fun _ -> Datom (fresh_delay_var ())) node.tn_input in
  let node_env =
    List.fold_left2
      (fun env (x, _) d -> StringMap.add x (fun () -> (Dprod d, Constraints.empty)) env)
      env node.tn_input d_inputs
  in
  (* Check each equation is well-initialized, starting from an empty constraint set. *)
  let rec loop cs (acc : d_prod StringMap.t) = function
    | [] -> (acc, cs)
    | eq :: eqs ->
        (* TODO : raise Initialization if there is a subtyping error. *)
        let res, cs = infer_equation node_env cs eq in
        let acc = List.fold_left (fun acc (v, d) -> StringMap.add v d acc) acc res in
        loop cs acc eqs
  in
  let map, cs = loop Constraints.empty StringMap.empty node.tn_equs in
  let d_outputs = List.map (fun (v, _) -> StringMap.find v map) node.tn_output in
  (* Compute the overall delay type of the node. *)
  let mk_bundle (ds : d_prod list) : d_prod =
    match ds with [ d ] -> d | ds -> Dtuple ds
  in
  let d_node = Dfunc (mk_bundle d_inputs, mk_bundle d_outputs) in
  Format.printf "RESULT %a |- %a@\n" Constraints.print cs print_d_type d_node;
  (* Add the node to the delay environment (but don't keep the node's variables in the environment). *)
  (* TODO : refresh (instantiate) the node's type in the thunk. *)
  StringMap.add node.tn_name (fun () -> (d_node, cs)) env

(** Check that all nodes in a file are well initialized.
    @raise Initialization if a node is not well initialized. *)
let check (file : t_file) : unit =
  ignore @@ List.fold_left check_node StringMap.empty file
