import AFTD.Prelude

/-!
# PetersenStripVertex

Topic: graphs   Node: a9d88062373d

Provenance: formalization of a published result. Source: arXiv:2610.24059

The vertex set of the infinite generalized Petersen strip, consisting of outer vertices u_i and inner vertices v_i indexed by integers i in ℤ.
-/

/-- Vertex type of the infinite generalized Petersen strip H_k, with outer vertices u_i and inner vertices v_i for i ∈ ℤ. -/
inductive PetersenStripVertex : Type | u (i : ℤ) : PetersenStripVertex
  | v (i : ℤ) : PetersenStripVertex
  deriving DecidableEq
