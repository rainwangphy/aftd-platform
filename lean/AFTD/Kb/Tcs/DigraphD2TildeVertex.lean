import AFTD.Prelude

/-!
# DigraphD2TildeVertex

Topic: combinatorics   Node: a72f67248152

Provenance: formalization of a published result. Source: arXiv:2611.15027 Section 5

The 6-element vertex type of the directed graph D̃₂, consisting of two base vertices u₁, u₂ and four vertices indexed by sign vectors in {-1, 1}².
-/

/-- Vertex set of the 6-vertex directed graph D̃₂ from arXiv:2611.15027. -/
inductive DigraphD2TildeVertex : Type where | u1 : DigraphD2TildeVertex
  | u2 : DigraphD2TildeVertex
  | v (eps1 eps2 : Bool) : DigraphD2TildeVertex
  deriving DecidableEq, Fintype
