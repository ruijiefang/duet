open Linear

val commuting_space : QQMatrix.t -> QQMatrix.t -> QQVectorSpace.t
val commuting_segment : QQMatrix.t array -> int list -> (QQMatrix.t * QQMatrix.t array)

type kind = Commute | Reset | Ignore

type phased_segment = {
   sim1 : QQMatrix.t;                 (* Simulation for phase 1 (all matrices commute) *)
   sim2 : QQMatrix.t;                 (* Simulation for phase 2 (all non-reset matrices commute) *)
   phase1 : QQMatrix.t array;         (* Image of each transition under the phase 1 simulation *)
   phase2 : (kind * QQMatrix.t) array (* Each transition i is either of kind Commute, in which case
                                         phase2.(i) is the image of transition i under the phase 1
                                         simulation, or of kind Reset, in which case phase2.(i) gives
                                         a representation of transition i as a transformation from the phase 1
                                         space to the phase 2 space *)
}

module PhasedSegment : sig
   type t = phased_segment

   val show : t -> string
   val equal : t -> t -> bool

   val make : (kind * QQMatrix.t) array -> t
end

type phased_segmentation = phased_segment list