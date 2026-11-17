import AFTD.Prelude

/-!
# op869_extend_colors

Topic: online_algorithms   Node: 243ddc8e2321

Provenance: helper lemma. Padding and monotonicity for the finite adversary game of arXiv:2610.41516 Section 2.

Extend color histories to a larger vertex universe by assigning no colors to new vertices.
-/

/-- Extend color histories to a larger vertex universe by assigning no colors to new vertices. -/
def op869_extend_colors {n m : ℕ} (h : n ≤ m) (C : Fin n → Finset ℕ)
    (v : Fin m) : Finset ℕ :=
  if hv : v.val < n then C ⟨v.val, hv⟩ else ∅
