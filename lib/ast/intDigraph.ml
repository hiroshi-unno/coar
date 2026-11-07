(* A mutable directed graph whose vertices are the integers the caller names,
   with its strongly connected components (ocamlgraph's concrete imperative
   digraph and [Components.Make] over it).

   Why not ocamlgraph's [Pack.Digraph]: its vertices are abstract, each
   [V.create] numbering its vertex from one process-global counter that is
   incremented and then read back without synchronisation, and two vertices
   with the same number are the same vertex to the graph.  When two domains
   create vertices at the same time -- the primal and dual tasks of a
   parallel fixpoint solver reduce their problems simultaneously -- one
   domain can hand out a number twice, so two distinct vertices of one graph
   merge: the merged vertex's edges are the union of both, and the components
   no longer partition the vertices, so a caller that maps every component
   back to its labels loses the label left out.  With integer vertices there
   is no shared state: a graph is a function of the edges added to it, so
   this module is safe to use from any number of domains at once, provided
   each graph value is used by one domain at a time.

   Contract of [Components.scc_list g]: a list of the strongly connected
   components of [g], each the non-empty list of its vertices; every vertex
   of [g] is in exactly one component.  The order of the components and of
   the vertices in each is ocamlgraph's (deterministic for a given sequence
   of insertions). *)
module Vertex = struct
  type t = int

  let compare = Stdlib.Int.compare
  let hash (x : int) = Stdlib.Hashtbl.hash x
  let equal = Stdlib.Int.equal
end

module G = Graph.Imperative.Digraph.Concrete (Vertex)
include G
module Components = Graph.Components.Make (G)
