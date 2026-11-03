import AFTD.Prelude

/-!
# colorsUsed

Topic: online_algorithms   Node: 7d934671decf

Provenance: formalization of a published result. Source: arXiv:2610.41516 Section 1

The number of distinct colors assigned by a vertex coloring c : Fin n → ℕ is the cardinality of the image of c on Finset.univ.
-/

/-- The number of distinct colors assigned by a vertex coloring c on Fin n. -/
def colorsUsed {n : ℕ} (c : Fin n → ℕ) : ℕ :=
  (Finset.univ.image c).card
