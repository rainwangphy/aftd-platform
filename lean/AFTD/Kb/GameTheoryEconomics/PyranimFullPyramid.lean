import AFTD.Prelude

/-!
# pyranim_full_pyramid

Topic: combinatorial_games   Node: c91c8d7c54eb

Provenance: formalization of a published result. Source: arXiv:2611.16153 Sec. 1.1

The finite set pyranim_full_pyramid n : Finset (ℕ × ℕ) of pairs of natural numbers (i, j) such that 1 ≤ i ≤ j ≤ n, defined by filtering (Finset.Icc 1 n) ×ˢ (Finset.Icc 1 n) with the predicate fun ⟨i, j⟩ => i ≤ j.
-/

/-- The finite set of chips in the full n-tier pyramid poset P_n = {[i, j] : 1 ≤ i ≤ j ≤ n}. -/
def pyranim_full_pyramid (n : ℕ) : Finset (ℕ × ℕ) := ((Finset.Icc 1 n) ×ˢ (Finset.Icc 1 n)).filter (fun ⟨i, j⟩ => i ≤ j)
