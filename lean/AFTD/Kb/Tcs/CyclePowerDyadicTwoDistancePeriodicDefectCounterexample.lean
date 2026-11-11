import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_two_distance_periodic_defect_counterexample

Topic: combinatorics   Node: 2082439433f0

Provenance: helper lemma. Counterexample to a restricted-coverage shortcut in the defective-half route for RT-1 and OP-205.

There is a period-one exponent-four tight defective profile with exact lower dyadic ownership, the defective top-owner and active-count equations, corrected lower-count periodicity, and coverage at both distances one and eleven, yet with a defect. It fails coverage at distance two and so does not refute the full-coverage conjecture.
-/

def rt1_two_dist_x (_ : ℤ) (a : ℕ) : Bool := (49161 : ℕ).testBit a
def rt1_two_dist_e (_ : ℤ) : Bool := true

theorem cycle_power_dyadic_two_distance_periodic_defect_counterexample :
  ∃ (y : ℤ → ℕ → Bool) (e : ℤ → Bool),
    (∀ p, cycle_power_dyadic_class_weight 4 (y p) = (Finset.range 16).sum (fun a => (y p a).toNat)) ∧
    (∀ j < 3, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (y (v-(a:ℤ)) a && y (v-(a:ℤ)) (a+16-2^j)).toNat) = 1) ∧
    (∀ v : ℤ, (Finset.range 8).sum (fun a =>
      (y (v-(a:ℤ)) a && y (v-(a:ℤ)) (a+8)).toNat) + (e v).toNat = 1) ∧
    (∀ v : ℤ, (Finset.range 16).sum (fun a => (y (v-(a:ℤ)) a).toNat) + (e v).toNat = 5) ∧
    (∀ v : ℤ, (Finset.range 8).sum (fun a => (y (v-(a:ℤ)) a).toNat) + (e v).toNat =
      (Finset.range 8).sum (fun a => (y (v+8-(a:ℤ)) a).toNat) + (e (v+8)).toNat) ∧
    (∀ v : ℤ, ∃ a : ℕ, a < 15 ∧ y (v-(a:ℤ)) a = true ∧ y (v-(a:ℤ)) (a+1) = true) ∧
    (∀ v : ℤ, ∃ a : ℕ, a < 5 ∧ y (v-(a:ℤ)) a = true ∧ y (v-(a:ℤ)) (a+11) = true) ∧
    e 0 = true ∧ ¬ (∃ a : ℕ, a < 14 ∧ y (-(a:ℤ)) a = true ∧ y (-(a:ℤ)) (a+2) = true) := by
  refine ⟨rt1_two_dist_x, rt1_two_dist_e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    change cycle_power_dyadic_class_weight 4 (fun a => (49161 : ℕ).testBit a) =
      (Finset.range 16).sum (fun a => ((49161 : ℕ).testBit a).toNat)
    decide
  · intro j hj v
    interval_cases j <;> simp only [rt1_two_dist_x] <;> decide
  · intro v
    simp only [rt1_two_dist_x, rt1_two_dist_e]
    decide
  · intro v
    simp only [rt1_two_dist_x, rt1_two_dist_e]
    decide
  · intro v
    simp [rt1_two_dist_x, rt1_two_dist_e]
  · intro v
    refine ⟨14, by decide, ?_, ?_⟩ <;> simp only [rt1_two_dist_x] <;> decide
  · intro v
    refine ⟨3, by decide, ?_, ?_⟩ <;> simp only [rt1_two_dist_x] <;> decide
  · decide
  · decide
