import AFTD.Prelude
import AFTD.Kb.Tcs.ValidCarpoolEdgeSequence

/-!
# CarpoolForestEdgeSequence

Topic: online_algorithms   Node: a93e01c8324e

Provenance: formalization of a published result. Source: arXiv:2611.00388: Online carpooling against an oblivious adversary; OP-1106

A list of edges on Fin n is an oblivious forest edge sequence for online carpooling if all edges connect distinct vertices, no undirected edge appears more than once, and the simple graph formed by the edges is acyclic.
-/

/-- A list of edges on Fin n is a carpool forest edge sequence if every edge connects distinct vertices, the undirected edges are pairwise distinct, and their union forms an acyclic simple graph (a forest). -/
def CarpoolForestEdgeSequence (n : ℕ) (edges : List (Fin n × Fin n)) : Prop := ValidCarpoolEdgeSequence n edges ∧
  (edges.map (fun e => s(e.1, e.2))).Nodup ∧
  (SimpleGraph.fromEdgeSet {s(e.1, e.2) | e ∈ edges}).IsAcyclic
