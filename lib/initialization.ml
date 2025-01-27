open Asttypes
open Typed_ast
open Delay_types

(** Exception raised when an expression is not properly initialized. *)
exception InitializationError of t_expr

(** Maps over strings. *)
module StringMap = Map.Make (String)

(** [mk_d_tuple [d_1; d_2; ...]] makes the delay type [(d_1, d_2, ...)].
    @raise Invalid_argument if a [d_i] is a function type. *)
let mk_d_tuple (ds : d_type list) : d_type =
  let raw_ds =
    List.map (function Dprod d -> d | _ -> raise @@ Invalid_argument "mk_d_tuple") ds
  in
  Dprod (Dtuple raw_ds)

(** Generate a [d_prod] with the same shape as a (normal) type. *)
let imitate_d_prod (f : unit -> d_atom) (t : ty) : d_prod =
  match t with
  | [ _ ] -> Datom (f ())
  | ts -> Dtuple (List.map (fun _ -> Datom (f ())) ts)

(**************************************************************************)
(** *** Delay Subtyping. *)
(**************************************************************************)

exception SubtypingError

(** The delay environment associates to each variable identifier a delay type scheme. *)
type d_env = d_scheme StringMap.t

(** Compute subtyping constraints on [d_atom].
    @raise SubtypingError if subtyping is impossible. *)
let d_atom_subtyping (cs : Constraints.t) (d1 : d_atom) (d2 : d_atom) : Constraints.t =
  match (d1, d2) with
  (* Trivial constraints : as an optimization, we don't add any constraint to the graph. *)
  | D0, _ | _, D1 -> cs
  (* Non-trivial constraints : add an edge to the graph and check it is still consistent. *)
  | _, _ ->
      let cs' = Constraints.add cs d1 d2 in
      if Constraints.consistent cs' then cs' else raise SubtypingError

(** Compute subtyping constraints on [d_prod].
    @raise SubtypingError if subtyping is impossible. *)
let rec d_prod_subtyping (cs : Constraints.t) (d1 : d_prod) (d2 : d_prod) : Constraints.t
    =
  match (d1, d2) with
  | Datom d1, Datom d2 -> d_atom_subtyping cs d1 d2
  | Dtuple d1s, Dtuple d2s when List.length d1s = List.length d2s ->
      List.fold_left2 d_prod_subtyping cs d1s d2s
  | _, _ ->
      Format.printf "d_prod error : %a and %a\n" print_d_prod d1 print_d_prod d2;
      raise SubtypingError

(** Compute subtyping constraints on [d_type].
    @raise SubtypingError if subtyping is impossible. *)
let d_type_subtyping (cs : Constraints.t) (d1 : d_type) (d2 : d_type) : Constraints.t =
  match (d1, d2) with
  | Dfunc (d1, d1'), Dfunc (d2, d2') ->
      (* Functions are contravariant in the argument and covariant in the result. *)
      let cs = d_prod_subtyping cs d2 d1 in
      d_prod_subtyping cs d1' d2'
  | Dprod d1, Dprod d2 -> d_prod_subtyping cs d1 d2
  | _, _ -> raise SubtypingError

(**************************************************************************)
(** *** Delay Inference. *)
(**************************************************************************)

(** [infer_unop cs op] returns a freshly instantiated delay type for unary operator [op].
*)
let infer_unop (cs : Constraints.t) (op : unop) : d_type * Constraints.t =
  match op with
  | Unot | Uminus | Uminus_f ->
      (* All unary operators we support have type [forall d. d -> d]. *)
      let d = Datom (Dvar (fresh_d_var ())) in
      (Dfunc (d, d), cs)

(** [infer_binop cs op] returns a freshly instantiated delay type for binary operator
    [op]. *)
let infer_binop (cs : Constraints.t) (op : binop) : d_type * Constraints.t =
  match op with
  | Beq | Bneq | Blt | Ble | Bgt | Bge | Badd | Bsub | Bmul | Badd_f | Bsub_f | Bmul_f
  | Band | Bor ->
      (* Most binary operators we support have type [forall d. d * d -> d]. *)
      let d = Datom (Dvar (fresh_d_var ())) in
      (Dfunc (Dtuple [ d; d ], d), cs)
  | Bdiv | Bmod | Bdiv_f ->
      (* Division and related operators have type [forall d. d * 0 -> d]. *)
      let d = Datom (Dvar (fresh_d_var ())) in
      (Dfunc (Dtuple [ d; Datom D0 ], d), cs)

(** [infer_app cs d_f d_arg app] comptutes a delay type for the application [app],
    assuming [d_f] and [d_arg] are the delay types of the function and argument. The
    expression [app] is not necessarily of the form [TE_app _] : it is used only for error
    reporting. This function requires computing subtyping constraints.

    @raise InitializationError
      for expression [app] if the subtyping constraints are inconsistent. *)
let infer_app (cs : Constraints.t) (d_f : d_type) (d_arg : d_type) (app : t_expr) :
    d_type * Constraints.t =
  match d_f with
  | Dprod _ -> failwith "d_type_app : expected a function type"
  | Dfunc (d_f_arg, d_f_res) -> begin
      try (Dprod d_f_res, d_type_subtyping cs d_arg (Dprod d_f_arg))
      with SubtypingError ->
        Format.printf "subtyping fail\ncs=%a\nd_arg=%a\nd_f_arg=%a\nd_f_res=%a\n"
          Constraints.print cs print_d_type d_arg print_d_prod d_f_arg print_d_prod
          d_f_res;
        raise @@ InitializationError app
    end

(** Infer a [d_type] for a variable or node by instantiating its delay type scheme. *)
let infer_ident (env : d_env) (cs : Constraints.t) (x : string) : d_type * Constraints.t =
  (* Lookup the identifier in the delay environment. *)
  match StringMap.find_opt x env with
  | Some scheme ->
      (* Instantiate the scheme. *)
      let cs_x, d_x = instantiate_scheme scheme in
      (* Accumulate the new constraints. *)
      let cs =
        List.fold_left
          (fun cs (d1, d2) -> Constraints.add cs d1 d2)
          cs (Constraints.to_list cs_x)
      in
      (d_x, cs)
  | None -> failwith @@ Format.sprintf "infer_ident : unbound identifier [%s]" x

(** [infer_expr env cs e] infers a delay type for expression [e] in delay environment
    [env] and with constraints [cs]. *)
let rec infer_expr (env : d_env) (cs : Constraints.t) (e : t_expr) :
    d_type * Constraints.t =
  (*let init_cs = cs in*)
  let res, cs =
    match e.texpr_desc with
    | TE_const _ ->
        (* Constants are always initialized. *)
        (Dprod (Datom D0), cs)
    | TE_ident x -> infer_ident env cs x
    | TE_unop (op, e1) ->
        let d_op, cs = infer_unop cs op in
        let d_e1, cs = infer_expr env cs e1 in
        infer_app cs d_op d_e1 e
    | TE_binop (op, e1, e2) ->
        let d_op, cs = infer_binop cs op in
        let d_args, cs = infer_tuple env cs [ e1; e2 ] in
        infer_app cs d_op d_args e
    | TE_app (f, es) ->
        let d_f, cs = infer_ident env cs f in
        let d_es, cs =
          match es with [ e ] -> infer_expr env cs e | es -> infer_tuple env cs es
        in
        infer_app cs d_f d_es e
    | TE_prim (_f, _es) -> failwith "infer_expr : TE_prim not implemented yet"
    | TE_if (e1, e2, e3) ->
        (* [if-then-else] has type [forall d. d * d * d -> d]. *)
        let d = Dvar (fresh_d_var ()) in
        let ds = imitate_d_prod (fun () -> d) e2.texpr_type in
        let d_if = Dfunc (Dtuple [ Datom d; ds; ds ], ds) in
        let d_args, cs = infer_tuple env cs [ e1; e2; e3 ] in
        infer_app cs d_if d_args e
    | TE_pre e1 ->
        (* [pre] has type [0 -> 1]. *)
        let zeros = imitate_d_prod (fun () -> D0) e1.texpr_type in
        let ones = imitate_d_prod (fun () -> D1) e1.texpr_type in
        let d_pre = Dfunc (zeros, ones) in
        let d_e1, cs = infer_expr env cs e1 in
        infer_app cs d_pre d_e1 e
    | TE_arrow (e1, e2) ->
        (* [->] has type [forall d. d * 1 -> d]. *)
        let ds = imitate_d_prod (fun () -> Dvar (fresh_d_var ())) e1.texpr_type in
        let ones = imitate_d_prod (fun () -> D1) e2.texpr_type in
        let d_arrow = Dfunc (Dtuple [ ds; ones ], ds) in
        let d_args, cs = infer_tuple env cs [ e1; e2 ] in
        infer_app cs d_arrow d_args e
    | TE_tuple es -> infer_tuple env cs es
    | TE_print es ->
        (* The printing function has type [forall d. (d * d * ...) -> d]. *)
        let d = Dvar (fresh_d_var ()) in
        let d_print =
          Dfunc
            ( Dtuple (List.map (fun e -> imitate_d_prod (fun () -> d) e.texpr_type) es)
            , Datom d )
        in
        let d_args, cs = infer_tuple env cs es in
        infer_app cs d_print d_args e
  in
  (*Format.printf "INFER %a : %a (%a ~~> %a)@\n" Typed_ast_printer.print_exp e print_d_type
    res Constraints.print init_cs Constraints.print cs;*)
  (res, cs)

(** Helper function to infer a [d_type] for a tuple of expressions, and assemble the
    resulting delays in a tuple. It assumes there are at least two expressions (i.e. it
    always returns a [Dtuple]). *)
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

(** Check the delay type for each variable bound by an equation. *)
let check_equation (env : d_env) (cs : Constraints.t) (eq : t_equation) : Constraints.t =
  (* Get the delay type of the pattern. *)
  let rec loop cs = function
    | [] -> ([], cs)
    | v :: vs ->
        let cs_v, d_v = instantiate_scheme (StringMap.find v env) in
        let d_vs, cs = loop (Constraints.union cs cs_v) vs in
        (d_v :: d_vs, cs)
  in
  let d_patt, cs = loop cs eq.teq_patt.tpatt_desc in
  let d_patt = match d_patt with [ d ] -> d | ds -> mk_d_tuple ds in
  (* Infer a delay type for the expression. *)
  let d_expr, cs = infer_expr env cs eq.teq_expr in
  (* Check subtyping holds. *)
  try d_type_subtyping cs d_expr d_patt
  with SubtypingError -> raise @@ InitializationError eq.teq_expr

(** Check a node is well initialized in a given delay environment, and add the node to the
    delay environment. This assumes the node has already been scheduled.
    @raise InitializationError if an expression is not well initialized. *)
let check_node (initial_env : d_env) (node : t_node) : d_env =
  Format.printf "@\nNODE %s@\n" node.tn_name;
  (* Add the node's inputs, output and local variables to the delay environment. 
     Careful : these variables are _not_ polymorphic, so the corresponding type schemes 
     do not quantify over any variables. *)
  let env =
    List.fold_left
      (fun env (x, _) ->
        let d = Dprod (Datom (Dvar (fresh_d_var ()))) in
        StringMap.add x ([], Constraints.empty, d) env)
      initial_env
      (node.tn_input @ node.tn_output @ node.tn_local)
  in
  (* Check each equation is well-initialized, starting from an empty constraint set. *)
  let cs = List.fold_left (check_equation env) Constraints.empty node.tn_equs in
  (* Compute the overall delay type scheme for the node. *)
  let d_vars vars =
    List.map
      begin
        fun (v, _) ->
          match StringMap.find v env with
          | [], _, Dprod d -> d
          | _ -> failwith "check_node : invalid type scheme for variable"
      end
      vars
  in
  (* Compute the overall delay type scheme of the node. *)
  let mk_bundle (ds : d_prod list) : d_prod =
    match ds with [ d ] -> d | ds -> Dtuple ds
  in
  let d_node =
    Dfunc (mk_bundle @@ d_vars node.tn_input, mk_bundle @@ d_vars node.tn_output)
  in
  (* Compute the quantified variables of the type scheme. *)
  let xs =
    DvarSet.union (Constraints.vars cs) (vars_d_type d_node)
    |> DvarSet.to_seq |> List.of_seq
  in
  (* Compute the node's type scheme. *)
  let scheme =
    (xs, cs, d_node) |> simplify_scheme_clamp |> simplify_scheme_filter
    |> simplify_scheme_bounds
  in
  Format.printf "@[scheme %a@\n@]" print_d_scheme scheme;
  StringMap.add node.tn_name scheme initial_env

(** Check that all nodes in a file are well initialized.
    @raise InitializationError if an expression is not well initialized. *)
let check (file : t_file) : unit =
  ignore @@ List.fold_left check_node StringMap.empty file
