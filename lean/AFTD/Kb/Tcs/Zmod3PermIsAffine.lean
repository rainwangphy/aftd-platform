import AFTD.Prelude

/-!
# zmod3_perm_is_affine

Topic: combinatorics   Node: b96e2b615ea6

Provenance: helper lemma. step towards ternary_minimal_line_cover_minimum_card_eq_hyperplane

Every bijection f : ZMod 3 → ZMod 3 is affine: there exist a, b ∈ ZMod 3 with a ≠ 0 such that f(t) = a * t + b for all t ∈ ZMod 3.
-/

/-- Every permutation of ZMod 3 is an affine map t ↦ a * t + b with a ≠ 0. -/
theorem zmod3_perm_is_affine (f : ZMod 3 → ZMod 3) (hf : Function.Bijective f) : ∃ (a b : ZMod 3), a ≠ 0 ∧ ∀ t, f t = a * t + b := by
  revert f
  decide
