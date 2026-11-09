import AFTD.Prelude

/-!
# ccz_star_graph

Topic: quantum_mechanics   Node: 865e6de0a121

Provenance: original. Related work: Mathlib/Combinatorics/SimpleGraph/Star.lean

For any natural number n, ccz_star_graph n is the star graph on Fin n with center at 0 (or the empty graph if n = 0).
-/

/-- The star graph on Fin n with center at 0. -/
def ccz_star_graph (n : ℕ) : SimpleGraph (Fin n) := if h : 0 < n then SimpleGraph.starGraph ⟨0, h⟩ else ⊥
