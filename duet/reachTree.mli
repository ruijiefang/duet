module TransitionSystem = Srk.TransitionSystem
module Syntax = Srk.Syntax 
module Interpretation = Srk.Interpretation 

type equery = OverApprox | UnderApprox

(** Implementation of an Abstract Reachability Tree (ART) for use in Duet's GPS algorithm implementation and Impact algorithm implementation
 *)
module ART
    (G : sig
       type t
       type vertex
       type weight
       val fold_succ :  (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
       val weight : t -> vertex -> vertex -> weight
       val summary : t -> vertex -> weight
       val compare_vertex : vertex -> vertex -> int
       val pp_vertex : Format.formatter -> vertex -> unit
     end)
    (L : sig
       type t
       val top : t
       val bottom : t
       val meet : t -> t -> t
       val leq : t -> t -> bool
       val pp : Format.formatter -> t -> unit
     end)
    (T : sig
       type t
       type label
       type state
       val check : label -> t list -> label -> [ `Valid of label list
                                               | `Invalid of state
                                               | `Unknown ]
       val post_model : state -> t -> state option
       val is_deterministic : t -> bool
       val mul : t -> t -> t
       val assume : label -> t
       val guard : t -> label
       val pp_state : Format.formatter -> state -> unit
     end with type t = G.weight
          and type label = L.t) : sig
  type node
  type t
  type state = T.state
  type weight = T.t
  type stats = {
    mutable num_covers_added : int;
    mutable num_covers_removed : int;
    mutable num_refinements_performed : int;
  }
  (** Creates an ART given a weighted graph, pre-condition, entry vertex [src] and exit vertex [dst] *)
  val make : G.t -> L.t -> src:G.vertex -> dst:G.vertex -> t

  (** Returns the entry vertex of the weighted graph *)
  val get_entry : t -> G.vertex 

  (** Returns the (distinguished) error vertex of the weighted graph *)
  val get_err_loc : t -> G.vertex

  (** Returns the pre-condition of the weighted graph *)
  val get_precondition : t -> L.t

  (** Prints out the ART to STDOUT *)
  val print_tree : t -> string -> node -> unit

  (** [parent t n] returns parent of node [n] inside tree [t] *)
  val parent : t -> node -> node

  (** given a node [n], [parent_weight t n] returns the weight of the edge from [parent t n] into n, if there exists a parent *)
  val parent_weight : t -> node -> (node * weight) option

  (** [maps_to t n] returns the weighted graph vertex corresponding to node [n] *)
  val maps_to : t -> node -> G.vertex
  
  (** mark a node as a frontier by adding it to end of frontiers queue *)
  val add_frontier : t -> node -> unit

  (** dequeue a frontier node from the queue of frontier nodes *)
  val deque_frontier : t -> node option

  (** [tree_path t src n] returns a list of nodes from [src] to [n], if [src] is [n]'s ancestor in [t], inclusive between [src] and [n]. *)
  val tree_path : t -> ?src:node -> node -> node list

  (** [is_leaf t n] returns true iff [n] is a leaf in the tree *)
  val is_leaf : t -> node -> bool

  (** return the tree label (state formula) at a given node *)
  val label : t -> node -> L.t

  (** expands ART at a given leaf location by traversing all successors of the corresponding weighted graph vertex *)
  val expand : t -> node -> unit

  (** (used by Impact algorithm) performs the close operation on the ART down a particular subtree *)
  val close : t -> node -> (bool * node list)

  (** (used by GPS) [forced_cover t u v] tries to force a covering between (u, v) on the same path *)
  val force_cover : t -> node -> node -> bool

  (** (used by GPS) a more lightweight version of Impact's close operation that only works on ancestors/children on the same path instead of subtrees *)
  val lclose : t -> node -> bool

  (** check if a node is covered by another node *)
  val is_covered : t -> node -> bool 

  (** performs refinement along a particular path *)
  val refine: t -> node list -> L.t list -> unit

  (** logs the ART to logging stream *)
  val log_art : t -> unit 

  (** logs the ART node to logging stream *)
  val log_node :  node -> unit 

  (** convert ART node into an integer *)
  val of_node : node -> int

  (** root of the entire tree *)
  val root : node

  (** pretty-prints a node of the ART *)
  val pp_node : Format.formatter -> node -> unit

  (** performs forward concrete execution from a given node in the tree *)
  val execute : t -> node -> T.state -> [ `Safe | `Unsafe of node ]

  (** returns a (potentially CRA-generated) summary from the given node to the error location in the weighted graph *)
  val path_to_error : t -> node -> weight

  (** returns a dynamically maintained statistics object *)
  val get_statistics : t -> stats 
end
