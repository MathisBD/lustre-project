open Asttypes
open Typed_ast

(**************************************************************************)
(** *** Delay Types. *)
(**************************************************************************)

(** Maps over strings. *)
module StringMap = Map.Make (String)

(** Atomic delay type. *)
type d_atom =
  | D0 (* Initialized at all time steps >= 0. *)
  | D1 (* Initialized at all time steps >= 1. *)
  | Dvar of int (* Delay variable. The integer is a unique identifier. *)

(** Tree of products of atomic delay types. *)
type d_prod = Datom of d_atom | Dtuple of d_prod list

(** Full delay types. *)
type d_type = Dprod of d_prod | Dfunc of d_prod * d_prod

(** [mk_d_tuple [d_1; d_2; ...]] makes the delay type [(d_1, d_2, ...)].
    @raise Invalid_argument if a [d_i] is a function type. *)
let rec mk_d_tuple (ds : d_type list) : d_type =
  let raw_ds =
    List.map (function Dprod d -> d | _ -> raise @@ Invalid_argument "mk_d_tuple") ds
  in
  Dprod (Dtuple raw_ds)

(**************************************************************************)
(** *** Delay Constraints. *)
(**************************************************************************)

(** A set of inequality constraints [d_i <= d_j] between atomic delays is represented as a
    directed graph : the constraint [d_i <= d_j] is encoded as an edge from [d_i] to
    [d_j]. *)
module Constraints : sig
  (** A set of constraints on atomic delays. *)
  type t

  (** The empty constraint set. *)
  val empty : t

  (** [add cs d1 d2] adds the constraints [d1 <= d2] to the constraint set [cs]. It does
      not check the result is consistent. *)
  val add : t -> d_atom -> d_atom -> t

  (** Check if a set of constraints is consistent, i.e. does not imply the inequality
      [D1 <= D0]. *)
  val consistent : t -> bool

  (** Convert a set of constraints to a list of constraints. *)
  val to_list : t -> (d_atom * d_atom) list
end = struct
  (** Ocamlgraph to use atomic delays as graph vertices. *)
  module V : Graph.Sig.COMPARABLE with type t = d_atom = struct
    type t = d_atom

    let equal d d' = d = d'
    let compare = compare
    let hash = Hashtbl.hash
  end

  (** Ocamlgraph module that implements directed persistent graphs with atomic delays as
      vertices. *)
  module G = Graph.Persistent.Digraph.Concrete (V)

  type t = G.t

  let empty = G.empty
  let add cs d1 d2 = G.add_edge cs d1 d2

  let consistent cs : bool =
    let module PathChecker = Graph.Path.Check (G) in
    not @@ PathChecker.check_path (PathChecker.create cs) D1 D0

  let to_list cs : (d_atom * d_atom) list =
    G.fold_edges (fun d1 d2 acc -> (d1, d2) :: acc) cs []
end

(**************************************************************************)
(** *** Delay Subtyping. *)
(**************************************************************************)

(** The delay environment associates to each variable identifier a thunk which returns :
    - a fresh delay type.
    - a set of constraints on the delay variables occuring in the above type.

    We use a thunk so that accessing the delay type of a variable always returns a new
    instantiation of the delay type and constraints. *)
type d_env = (unit -> d_type * Constraints.t) StringMap.t

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
    [env] and with constraints [cs]. *)
let rec infer_expr (env : d_env) (cs : Constraints.t) (e : t_expr) :
    d_type * Constraints.t =
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

(** Main entry-point : check a node is well initialized in a given delay environment, and
    compute its delay type. *)
(*let is_node_initialized (env : delay_env) (node : t_node) : bool =
  (* Compute the initial delay environment for this node, which contains the node's inputs 
     and local variables. *)
  let env =
    List.fold_left
      (fun env (x, _) ->
        StringMap.add x (Dprod [ fresh_delay_var () ], empty_constraints) env)
      env
      (node.tn_input @ node.tn_local)
  in
  (* Check each equation is well-initialized. *)
  true*)
