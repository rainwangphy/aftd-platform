import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteRamseyProperty

/-!
# bipartite_ramsey_number

Topic: graphs   Node: b56b439e5b6c

Provenance: formalization of a published result. Source: arXiv:2610.29813

The r-colour bipartite Ramsey number br_r(H) of a simple graph H is the infimum of the set of natural numbers N such that every r-edge-colouring of K_{N,N} contains a monochromatic copy of H.
-/

/-- The r-colour bipartite Ramsey number br_r(H) of a simple graph H. -/
noncomputable def bipartite_ramsey_number {α : Type*} (H : SimpleGraph α) (r : ℕ) : ℕ :=
  sInf {N : ℕ | bipartite_ramsey_property H r N}
