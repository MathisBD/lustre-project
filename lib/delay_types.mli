(** Delay variables are encoded using a unique (numerical) identifier. *)
type d_var = int

module DvarSet : Set.S with type elt = d_var

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

  (** [union cs1 cs2] takes the union of [cs1] and [cs2]. *)
  val union : t -> t -> t

  (** Check if a set of constraints is consistent, i.e. does not imply the inequality
      [D1 <= D0]. *)
  val consistent : t -> bool

  (** Convert a set of constraints to a list of constraints. *)
  val to_list : t -> (d_atom * d_atom) list

  (** Compute the set of all variables in a constraint set. *)
  val vars : t -> DvarSet.t

  (** Print a set of constraints. *)
  val print : Format.formatter -> t -> unit
end

(** Delay type schemes. [(xs, cs, d)] encodes the type scheme [forall xs : cs, d]. *)
type d_scheme = d_var list * Constraints.t * d_type

(** Compute the set of all variables in a [d_type]. *)
val vars_d_type : d_type -> DvarSet.t

(** Generate a fresh delay variable. *)
val fresh_d_var : unit -> d_var

(** Instantiate a delay type scheme, i.e. replace all quantified delay variables by fresh
    delay variables. *)
val instantiate_scheme : d_scheme -> Constraints.t * d_type

(** Remove useless information contained in a type scheme :
    - remove trivial constraints.
    - remove any quantified variable which is not present in the delay type or
      constraints. *)
val tidy_scheme : d_scheme -> d_scheme

(** * Printing. *)

val print_d_atom : Format.formatter -> d_atom -> unit
val print_d_prod : Format.formatter -> d_prod -> unit
val print_d_type : Format.formatter -> d_type -> unit
val print_d_scheme : Format.formatter -> d_scheme -> unit

(** * Substitutions. *)

(** Apply a substitution (a function of type [d_var -> d_atom]) on a [d_type]. *)
val subst_d_type : (d_var -> d_atom) -> d_type -> d_type

(** Apply a substitution (a function of type [d_var -> d_atom]) on a [d_prod]. *)
val subst_d_prod : (d_var -> d_atom) -> d_prod -> d_prod

(** Apply a substitution (a function of type [d_var -> d_atom]) on a [d_atom]. *)
val subst_d_atom : (d_var -> d_atom) -> d_atom -> d_atom

(** Apply a substitution (a function of type [d_var -> d_atom]) to a set of constraints.
*)
val subst_constraints : (d_var -> d_atom) -> Constraints.t -> Constraints.t

(** * Simplifying constraints. *)

(** For each delay variable [d] such that [d <= 0] (resp. [1 <= d]), replace [d] by [0]
    (resp. by [1]). *)
val simplify_scheme_clamp : d_scheme -> d_scheme

(** In a type scheme [(xs, cs, d)], remove delay variables which do not appear in [d], and
    modify the constraint graph [cs] accordingly so that no constraints are lost. *)
val simplify_scheme_filter : d_scheme -> d_scheme

(** Replace all input (contra-variant) delay variables by their upper bound and all output
    (co-variant) delay variables by their lower bound. Variables are processed one after
    the other, until a fixpoint is reached. The computation of lower/upper bounds is quite
    basic : in particular this procedure does not create new variables, it only removes
    variables.

    This can be an expensive operation. *)
val simplify_scheme_bounds : d_scheme -> d_scheme
