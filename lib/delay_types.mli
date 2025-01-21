(** Delay variables are encoded using a unique (numerical) identifier. *)
type d_var = int

(** Atomic delay type. *)
type d_atom =
  (* Initialized at all time steps >= 0. *)
  | D0
  (* Initialized at all time steps >= 1. *)
  | D1
  (* Delay variable. *)
  | Dvar of d_var

(** Tree of products of atomic delay types. *)
type d_prod = Datom of d_atom | Dtuple of d_prod list

(** Full delay types. *)
type d_type = Dprod of d_prod | Dfunc of d_prod * d_prod

(** A set of inequality constraints [d_i <= d_j] between atomic delays is represented as a
    directed graph : the constraint [d_i <= d_j] is encoded as an edge from [d_i] to
    [d_j]. *)
module Constraints : sig
  (** A set of constraints on atomic delays. *)
  type t

  (** The empty constraint set. *)
  val empty : t

  (** Check if a constraint set is empty. *)
  val is_empty : t -> bool

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

(** Delay type schemes. [(xs, cs, d)] encodes the type scheme [forall xs : cs, d]. *)
type d_scheme = d_var list * Constraints.t * d_type

(** Generate a fresh delay variable. *)
val fresh_d_var : unit -> d_var

(** Instantiate a delay type scheme, i.e. replace all quantified delay variables by fresh
    delay variables. *)
val instantiate_d_scheme : d_scheme -> Constraints.t * d_type

val print_d_atom : Format.formatter -> d_atom -> unit
val print_d_prod : Format.formatter -> d_prod -> unit
val print_d_type : Format.formatter -> d_type -> unit
val print_d_scheme : Format.formatter -> d_scheme -> unit
