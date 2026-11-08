import AFTD.Prelude

/-!
# affine_func_at_most_one_root

Topic: combinatorics   Node: bde8734193af

Provenance: helper lemma. folklore

A nonzero affine function t ↦ a + b * t with b ≠ 0 has at most one real root.
-/

/-- A nonzero affine function has at most one real root. -/
theorem affine_func_at_most_one_root (a b : ℝ) (hb : b ≠ 0) (s : Finset ℝ)
    (hs : ∀ t ∈ s, a + b * t = 0) : s.card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro t₁ t₂ ht₁ ht₂
  apply mul_left_cancel₀ hb
  linarith [hs t₁ ht₁, hs t₂ ht₂]
