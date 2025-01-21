open Format

type d_atom = D0 | D1 | Dvar of int
type d_prod = Datom of d_atom | Dtuple of d_prod list
type d_type = Dprod of d_prod | Dfunc of d_prod * d_prod

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

(**************************************************************************)
(** *** Delay Constraints. *)
(**************************************************************************)

module Constraints = struct
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
