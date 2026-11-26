import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerFifteenModelNoIsland
import AFTD.Kb.Tcs.CyclePowerThirtyOneModelNoIsland
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_optimal_count_no_middle_island_small

Topic: combinatorics   Node: ca720c293bf9

Provenance: helper lemma. Helper step for the main statement of OP-205 (arXiv:2610.15635, the case k+1 = 2^m, n even, (k+1) not dividing n, left open there); it concerns the integer Boolean class models that optimal (m+1)-layer covers give. Base cases of the island exclusion, from the no-island theorems at exponents 4 and 5.

The cases j = 1 and j = 2 (exponents 4 and 5) of cycle_power_dyadic_optimal_count_no_middle_island: with D = 2^(j+3) and g = 2^j, in a tight, exactly dyadically covered, fully covered integer Boolean class model at exponent j+3 with exactly j+4 active classes at every vertex, no class is the island [0, g) ∪ [3g, 5g) ∪ [7g, D).
-/

theorem cycle_power_dyadic_optimal_count_no_middle_island_small (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 2)
    (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (j+3) (x p) =
      (Finset.range (2^(j+3))).sum (fun a => (x p a).toNat))
    (hexact : ∀ i < j+3, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(j+3)-2^i)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(j+3) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(j+3)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(j+3))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (j+3)+1) :
    ∀ p : ℤ, ¬ ∀ b < 2^(j+3), x p b = (decide (b < 2^j) || (decide (3*2^j ≤ b) && decide (b < 5*2^j)) || decide (7*2^j ≤ b)) := by
  intro p hI
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
  · have h2 := hI 2 (by norm_num)
    have h6 := hI 6 (by norm_num)
    have h10 := hI 10 (by norm_num)
    have h := cycle_power_fifteen_model_no_island x htight hexact hcover hcount p 2 6 10
      (by norm_num) (by norm_num) (by norm_num) (by rw [h2]; decide) (by rw [h6]; decide)
    rw [h10] at h
    revert h; decide
  · have h4 := hI 4 (by norm_num)
    have h12 := hI 12 (by norm_num)
    have h20 := hI 20 (by norm_num)
    have h := cycle_power_thirty_one_model_no_island x htight hexact hcover hcount p 4 12 20
      (by norm_num) (by norm_num) (by norm_num) (by rw [h4]; decide) (by rw [h12]; decide)
    rw [h20] at h
    revert h; decide
