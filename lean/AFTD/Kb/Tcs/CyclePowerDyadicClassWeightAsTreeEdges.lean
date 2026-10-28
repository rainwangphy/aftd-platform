import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_class_weight_as_tree_edges

Topic: combinatorics   Node: e1aa94965e3f

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

For a positive-exponent dyadic profile containing both endpoints, its weighted class count is one plus its unweighted number of selected dyadic pairs over all ranks.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_class_weight_as_tree_edges
    (m : ℕ) (hm : 1 ≤ m) (b : ℕ → Bool)
    (hends : b 0 = true ∧ b (2^m-1) = true) :
    cycle_power_dyadic_class_weight m b = 1 + (range m).sum (fun j =>
      (range (2^j)).sum (fun a => (b a && b (a+2^m-2^j)).toNat)) := by
  let f : ℕ → ℕ := fun j => (range (2^j)).sum
    (fun a => (b a && b (a+2^m-2^j)).toNat)
  have hf₀ : f 0 = 1 := by simp only [f, pow_zero, sum_range_one, zero_add, hends.1, hends.2,
    Bool.true_and, Bool.toNat_true]
  have hi : (range m).sum (fun j => if j = 0 then 1 else 0) = 1 := by
    simp [show 0 < m by omega]
  have hp (j : ℕ) : (if j = 0 then 0 else f j) + (if j = 0 then 1 else 0) = f j := by
    by_cases hj : j = 0
    · subst j
      simp [hf₀]
    · simp only [if_neg hj, add_zero]
  have hs := sum_congr rfl (fun j (hj : j ∈ range m) => hp j)
  rw [sum_add_distrib, hi] at hs
  simp only [cycle_power_dyadic_class_weight, hends.1, hends.2, Bool.true_and, Bool.toNat_true, mul_one]
  change 2 + (range m).sum (fun j => if j = 0 then 0 else f j) =
    1 + (range m).sum f
  omega
