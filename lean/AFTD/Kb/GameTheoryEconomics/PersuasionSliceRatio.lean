import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionSlicePrior
import AFTD.Kb.GameTheoryEconomics.PersuasionMaxReceiverUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionPriorUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceValues

/-!
# persuasion_slice_ratio

Topic: mechanism_design   Node: 2daf6ddb411c

The slice prior attains ratio (3m+1)/(2m+2). For the prior uniform over the 2m+1 states of persuasion_slice_prior m (coordinates = m-subsets of a (2m+1)-set), R_max / R_0 = (3m+1)/(2m+2) = 3/2 - 1/(m+1). For m = 4 this is 13/10 > 39/31.
-/

open Finset in
/-- `(m+1) C(2m+1, m) = 2 (2m+1) C(2m-1, m)` for `m ≥ 1`. -/
lemma persuasion_slice_choose_identity (m : ℕ) (hm : 1 ≤ m) :
    (m + 1) * (2 * m + 1).choose m = 2 * (2 * m + 1) * (2 * m - 1).choose m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have c1 : (2 * (k + 1)).choose (k + 1) = 2 * (2 * (k + 1) - 1).choose (k + 1) := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.choose_succ_succ,
      show 2 * k + 1 + 1 - 1 = 2 * k + 1 by omega]
    have : (2 * k + 1).choose k = (2 * k + 1).choose (k + 1) := by
      rw [← Nat.choose_symm (by omega : k ≤ 2 * k + 1)]; congr 1; omega
    rw [this]; ring
  have h := Nat.add_one_mul_choose_eq (2 * (k + 1)) (k + 1)
  have hs : (2 * (k + 1) + 1).choose (k + 1 + 1) = (2 * (k + 1) + 1).choose (k + 1) := by
    rw [← Nat.choose_symm (by omega : k + 1 + 1 ≤ 2 * (k + 1) + 1)]; congr 1; omega
  rw [hs, c1] at h
  linarith

open Finset in
/-- **The slice prior attains ratio `(3m+1)/(2m+2)`.** For the prior uniform over the `2m+1`
states of `persuasion_slice_prior m` (coordinates = `m`-subsets of a `(2m+1)`-set),
`R_max / R_0 = (3m+1)/(2m+2) = 3/2 - 1/(m+1)`. For `m = 4` this is `13/10 > 39/31`. -/
theorem persuasion_slice_ratio (m : ℕ) (hm : 1 ≤ m) :
    2 * (m + 1) * persuasion_max_receiver_utility (persuasion_slice_prior m) =
        (3 * m + 1) * persuasion_prior_utility (persuasion_slice_prior m) ∧
      0 < persuasion_prior_utility (persuasion_slice_prior m) := by
  obtain ⟨h1, h2⟩ := persuasion_slice_values m hm
  have hid : ((m : ℝ) + 1) * (2 * m + 1).choose m = 2 * (2 * m + 1) * (2 * m - 1).choose m := by
    exact_mod_cast persuasion_slice_choose_identity m hm
  have hK : (0 : ℝ) < 2 * m + 1 := by positivity
  have hn : (0 : ℝ) < (2 * m + 1).choose m := by exact_mod_cast Nat.choose_pos (by omega)
  rw [h1, h2]
  refine ⟨?_, by positivity⟩
  field_simp
  nlinarith [hid]
