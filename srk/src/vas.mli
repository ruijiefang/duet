(** Rational Vector Addition System with Resets Abstract Domain.  A
   rational vector addition system with resets is a set of \{0,
   1\}{^n} x QQ{^n} vector pairs. Each object describes a reset or
   increment to n counters. *)
open Syntax
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector

type transformer =
  { a : Z.t;
    b : V.t }
[@@deriving ord, show]
module TSet : BatSet.S with type elt = transformer
type vas = TSet.t
type 'a t = { v : vas; s_lst : M.t list}
val gamma : 'a context ->  'a t -> (symbol * symbol) list -> 'a formula
val abstract : 'a Iteration.Solver.t -> 'a t
val pp : 'a Iteration.Solver.t -> Format.formatter -> 'a t -> unit
val exp_t : 'a Iteration.Solver.t -> 'a t -> 'a arith_term -> 'a formula
val exp : 'a Iteration.exp_op

(* TODO: remove exp_base_helper *)
val exp_base_helper : 'a context -> (symbol * Symbol.Map.key) list -> 'a arith_term ->
  M.t list -> transformer list -> 
  'a formula * (('a arith_term list * ('a arith_term * Z.dim) list * 'a arith_term * 'a arith_term)
                  list * 'a arith_term list list * 'a arith_term list)

(* TODO: remove exp_other_reset_helper *)
val exp_other_reset_helper : 'a context -> 'a arith_term -> 'a arith_term list -> 'a arith_term list list 
  -> int -> 'a formula

val term_list : 'a context -> M.t list -> (symbol * Symbol.Map.key) list -> 
  (('a, typ_arith) expr * 'a arith_term) list
val gamma_transformer : 'a context -> ('a arith_term * 'a arith_term) list -> transformer -> 'a formula
val alpha_hat  : 'a context -> 'a formula -> (symbol * symbol) list ->  'c t
val coprod_compute_image : TSet.t -> M.t list -> TSet.t
val coprod_find_transformation : M.t list -> M.t list -> 
  Linear.QQMatrix.t list * Linear.QQMatrix.t list * M.t list


(** Monotone approximation of transitive closure based on Q-VASR.  The
   transitions of the input transition formula are partitioned by the
   direction of each variable (increasing, decreasing, or stable) and
   there is one transition per cell. *)
module Monotone : Iteration.Domain
