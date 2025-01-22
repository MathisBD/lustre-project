open Format
module IntMap = Map.Make (Int)

type d_var = int
type d_atom = D0 | D1 | Dvar of d_var
type d_prod = Datom of d_atom | Dtuple of d_prod list
type d_type = Dprod of d_prod | Dfunc of d_prod * d_prod

let fresh_d_var : unit -> d_var =
  let counter = ref 0 in
  fun () ->
    counter := !counter + 1;
    !counter

let print_d_atom fmt d : unit =
  match d with
  | D0 -> fprintf fmt "0"
  | D1 -> fprintf fmt "1"
  | Dvar x -> fprintf fmt "d%d" x

let rec print_d_prod fmt d : unit =
  match d with
  | Datom d -> print_d_atom fmt d
  | Dtuple ds ->
      let rec loop fmt = function
        | [] -> ()
        | [ d ] -> fprintf fmt "%a" print_d_prod d
        | d :: ds -> fprintf fmt "%a * %a" print_d_prod d loop ds
      in
      fprintf fmt "(%a)" loop ds

let print_d_type fmt d : unit =
  match d with
  | Dfunc (d1, d2) -> fprintf fmt "%a -> %a" print_d_prod d1 print_d_prod d2
  | Dprod d -> print_d_prod fmt d

module DvarSet : Set.S with type elt = d_var = Set.Make (struct
  include Int
end)

(** Accumulate the set of _all_ variables in a [d_atom]. *)
let vars_d_atom (acc : DvarSet.t) (d : d_atom) : DvarSet.t =
  match d with D0 | D1 -> acc | Dvar v -> DvarSet.add v acc

(** Accumulate the set of _all_ variables in a [d_prod]. *)
let rec vars_d_prod (acc : DvarSet.t) (d : d_prod) : DvarSet.t =
  match d with
  | Dtuple ds -> List.fold_left vars_d_prod acc ds
  | Datom d -> vars_d_atom acc d

(** Accumulate the set of _all_ variables in a [d_type]. *)
let vars_d_type (d : d_type) : DvarSet.t =
  match d with
  | Dfunc (d1, d2) ->
      let acc = vars_d_prod DvarSet.empty d1 in
      vars_d_prod acc d2
  | Dprod d -> vars_d_prod DvarSet.empty d

(** Accumulate the set of _positive_ variables in a [d_type]. *)
let pos_vars_d_type (acc : DvarSet.t) (d : d_type) : DvarSet.t =
  match d with Dfunc (_, d2) -> vars_d_prod acc d2 | Dprod d -> vars_d_prod acc d

(** Accumulate the set of _negative_ variables in a [d_type]. *)
let neg_vars_d_type (acc : DvarSet.t) (d : d_type) : DvarSet.t =
  match d with Dfunc (d1, _) -> vars_d_prod acc d1 | Dprod d -> vars_d_prod acc d

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

module GOps = Graph.Oper.P (G)

module Constraints = struct
  type t = G.t

  let empty = G.empty
  let is_empty = G.is_empty
  let add cs d1 d2 = G.add_edge cs d1 d2
  let union cs1 cs2 = G.fold_edges (fun d1 d2 acc -> G.add_edge acc d1 d2) cs2 cs1

  let consistent cs : bool =
    if (not (G.mem_vertex cs D0)) || not (G.mem_vertex cs D1)
    then true
    else
      let module PathChecker = Graph.Path.Check (G) in
      not @@ PathChecker.check_path (PathChecker.create cs) D1 D0

  let filter f cs : t =
    G.fold_edges
      (fun d1 d2 acc -> if f d1 d2 then G.add_edge acc d1 d2 else acc)
      cs G.empty

  let to_list cs : (d_atom * d_atom) list =
    G.fold_edges (fun d1 d2 acc -> (d1, d2) :: acc) cs []

  let vars cs : DvarSet.t =
    G.fold_vertex
      (fun v acc -> match v with D0 | D1 -> acc | Dvar v -> DvarSet.add v acc)
      cs DvarSet.empty

  let print fmt cs : unit =
    let rec loop fmt = function
      | [] -> ()
      | [ (d1, d2) ] -> fprintf fmt "%a <= %a" print_d_atom d1 print_d_atom d2
      | (d1, d2) :: ds ->
          fprintf fmt "%a <= %a,@ %a" print_d_atom d1 print_d_atom d2 loop ds
    in
    fprintf fmt "@[{%a}@]" loop (to_list cs)
end

type d_scheme = d_var list * Constraints.t * d_type

let rec print_d_scheme fmt (xs, cs, d) : unit =
  if xs <> [] then fprintf fmt "forall %a. " print_vars xs;
  if not (Constraints.is_empty cs) then fprintf fmt "%a " Constraints.print cs;
  fprintf fmt "%a" print_d_type d

and print_vars fmt = function
  | [] -> ()
  | [ v ] -> fprintf fmt "%a" print_d_atom (Dvar v)
  | v :: vs -> fprintf fmt "%a %a" print_d_atom (Dvar v) print_vars vs

let rec subst_d_type subst = function
  | Dfunc (d1, d2) -> Dfunc (subst_d_prod subst d1, subst_d_prod subst d2)
  | Dprod d -> Dprod (subst_d_prod subst d)

and subst_d_prod subst = function
  | Dtuple ds -> Dtuple (List.map (subst_d_prod subst) ds)
  | Datom d -> Datom (subst_d_atom subst d)

and subst_d_atom subst = function D0 -> D0 | D1 -> D1 | Dvar d -> subst d

let subst_constraints subst cs : Constraints.t =
  G.fold_edges
    (fun d1 d2 acc -> G.add_edge acc (subst_d_atom subst d1) (subst_d_atom subst d2))
    cs G.empty

let instantiate_scheme (xs, cs, d) : Constraints.t * d_type =
  let map =
    List.fold_left (fun subst x -> IntMap.add x (fresh_d_var ()) subst) IntMap.empty xs
  in
  let subst d = match IntMap.find_opt d map with Some d' -> Dvar d' | None -> Dvar d in
  (subst_constraints subst cs, subst_d_type subst d)

let tidy_scheme ((xs, cs, d) : d_scheme) : d_scheme =
  (* Remove trivial edges. *)
  let cs = Constraints.filter (fun d1 d2 -> not (d1 = d2 || d1 = D0 || d2 = D1)) cs in
  (* Trim the quantifiers. *)
  let kept_vars = DvarSet.union (Constraints.vars cs) (vars_d_type d) in
  let xs = List.filter (fun x -> DvarSet.mem x kept_vars) xs in
  (xs, cs, d)

let simplify_scheme_clamp ((xs, cs, d) : d_scheme) : d_scheme =
  (* Take the transitive closure of the constraint graph. *)
  let cs = GOps.transitive_closure cs in
  (* Figure out which variables we can replace by [D0] or [D1]. *)
  let map =
    G.fold_edges
      begin
        fun d1 d2 map ->
          match (d1, d2) with
          | Dvar v1, D0 -> IntMap.add v1 D0 map
          | D1, Dvar v2 -> IntMap.add v2 D1 map
          | _ -> map
      end
      cs IntMap.empty
  in
  let subst v = try IntMap.find v map with Not_found -> Dvar v in
  (* Apply the substitution. *)
  tidy_scheme (xs, subst_constraints subst cs, subst_d_type subst d)

(** Constraint simplification by garbage collection. The idea is to take the transitive
    closure of the constraint set, and then to aggressively filter edges. *)
let simplify_scheme_filter ((xs, cs, d) : d_scheme) : d_scheme =
  (* Take the transitive closure of the constraint graph. *)
  let cs = GOps.transitive_closure cs in
  (* Filter out some constraints. *)
  let d_vars = vars_d_type d in
  let keep_edge d1 d2 : bool =
    match (d1, d2) with
    | Dvar v, _ when not @@ DvarSet.mem v d_vars -> false
    | _, Dvar v when not @@ DvarSet.mem v d_vars -> false
    | _ -> true
  in
  let cs = Constraints.filter keep_edge cs in
  (* Take the transitive reduction of the constraint graph. *)
  let cs = GOps.transitive_reduction cs in
  (* Return the new type scheme. *)
  tidy_scheme (xs, cs, d)

module DatomSet = Set.Make (struct
  type t = d_atom

  let compare = compare
end)

let simplify_scheme_bounds ((xs, cs, d) : d_scheme) : d_scheme =
  let all_vars = DvarSet.union (Constraints.vars cs) (vars_d_type d) in
  (* We have to normalize the constraint graph :
     - add all variables from the delay type.
     - add all edges from [D0] and all edges to [D1].
     - take the transitive closure. *)
  let cs_clos =
    DvarSet.fold
      (fun v acc ->
        let acc = G.add_edge acc D0 (Dvar v) in
        G.add_edge acc (Dvar v) D1)
      all_vars cs
  in
  let cs_clos = GOps.transitive_closure cs_clos in
  (* Helper functions to compute the least upper bound and greatest lower bound of a node. *)
  let leq d d' : bool = d = d' || G.mem_edge cs_clos d d' in
  let lub (v : d_atom) : d_atom option =
    let succs = G.succ cs_clos v in
    List.find_opt (fun s -> List.for_all (fun s' -> leq s s') succs) succs
  in
  let glb (v : d_atom) : d_atom option =
    let preds = G.pred cs_clos v in
    List.find_opt (fun p -> List.for_all (fun p' -> leq p' p) preds) preds
  in
  (* Compute the positive and negative variables of the delay type. *)
  let pos_vars = pos_vars_d_type DvarSet.empty d in
  let neg_vars = neg_vars_d_type DvarSet.empty d in
  (* Replace variables as needed. *)
  let on_var (d : d_var) (map : d_atom IntMap.t) =
    match d with
    (* Negative variables are replaced by their least upper bound (if it exists). *)
    | v when DvarSet.mem v neg_vars -> begin
        match lub (Dvar v) with None -> map | Some v' -> IntMap.add v v' map
      end
    (* Positive variables are replaced by their greatest lower bound (if it exists). *)
    | v when DvarSet.mem v pos_vars -> begin
        match glb (Dvar v) with None -> map | Some v' -> IntMap.add v v' map
      end
    (* Neutral variables are kept unchanged. *)
    | _ -> map
  in
  let map = DvarSet.fold on_var all_vars IntMap.empty in
  let subst (v : d_var) : d_atom = try IntMap.find v map with Not_found -> Dvar v in
  tidy_scheme (xs, subst_constraints subst cs, subst_d_type subst d)
