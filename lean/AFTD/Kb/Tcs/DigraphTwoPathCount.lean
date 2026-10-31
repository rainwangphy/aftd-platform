import AFTD.Prelude

/-!
# digraph_two_path_count

Topic: graphs   Node: 910b85ce48ec

Provenance: formalization of a published result. Source: arXiv:2610.39702, Section 2.1

The number of directed paths of length two from u to v in a finite directed graph D, defined as the number of vertices w such that D has an arc from u to w and an arc from w to v.
-/

/-- The number of directed paths of length two from u to v in a finite directed graph. -/
def digraph_two_path_count {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj] (u v : V) : ℕ := (Finset.univ.filter (fun w => D.Adj u w ∧ D.Adj w v)).card
