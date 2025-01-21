(**************************************************************************)
(** *** Delay Types. *)
(**************************************************************************)

(** Atomic delay type. *)
type d_atom =
  (* Initialized at all time steps >= 0. *)
  | D0
  (* Initialized at all time steps >= 1. *)
  | D1
  (* Delay variable. The integer is a unique identifier. *)
  | Dvar of int

(** Tree of products of atomic delay types. *)
type d_prod = Datom of d_atom | Dtuple of d_prod list

(** Full delay types. *)
type d_type = Dprod of d_prod | Dfunc of d_prod * d_prod

val print_d_atom : Format.formatter -> d_atom -> unit
val print_d_prod : Format.formatter -> d_prod -> unit
val print_d_type : Format.formatter -> d_type -> unit

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

  (** Print a set of constraints. *)
  val print : Format.formatter -> t -> unit
end
