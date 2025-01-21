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

module Constraints = struct
  type t = G.t

  let empty = G.empty
  let is_empty = G.is_empty
  let add cs d1 d2 = G.add_edge cs d1 d2

  let consistent cs : bool =
    if (not (G.mem_vertex cs D0)) || not (G.mem_vertex cs D1)
    then true
    else
      let module PathChecker = Graph.Path.Check (G) in
      not @@ PathChecker.check_path (PathChecker.create cs) D1 D0

  let to_list cs : (d_atom * d_atom) list =
    G.fold_edges (fun d1 d2 acc -> (d1, d2) :: acc) cs []

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
  | [ v ] -> fprintf fmt "%d" v
  | v :: vs -> fprintf fmt "%d %a" v print_vars vs

(** Apply a renaming (a function of type [d_var -> d_var]) on a [d_type]. *)
let rec rename_d_type subst = function
  | Dfunc (d1, d2) -> Dfunc (rename_d_prod subst d1, rename_d_prod subst d2)
  | Dprod d -> Dprod (rename_d_prod subst d)

(** Apply a renaming (a function of type [d_var -> d_var]) on a [d_prod]. *)
and rename_d_prod subst = function
  | Dtuple ds -> Dtuple (List.map (rename_d_prod subst) ds)
  | Datom d -> Datom (rename_d_atom subst d)

(** Apply a renaming (a function of type [d_var -> d_var]) on a [d_atom]. *)
and rename_d_atom subst = function D0 -> D0 | D1 -> D1 | Dvar d -> Dvar (subst d)

(** Apply a renaming (a function of type [d_var -> d_var]) to a set of constraints. *)
let rename_constraints subst cs : Constraints.t = G.map_vertex (rename_d_atom subst) cs

let instantiate_d_scheme (xs, cs, d) : Constraints.t * d_type =
  let map =
    List.fold_left (fun subst x -> IntMap.add x (fresh_d_var ()) subst) IntMap.empty xs
  in
  let subst d = match IntMap.find_opt d map with Some d' -> d' | None -> d in
  (rename_constraints subst cs, rename_d_type subst d)
