import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicHalfMonotoneOfMiddleFullPrune
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_half_monotone_of_middle_full_and_pruned_mono

Topic: combinatorics   Node: f4972a7b45c3

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

Current middle-bit fullness and monotonicity of both halves of the pruned model imply monotonicity of both original halves, in a tight exact full ordinary-cover model.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_half_monotone_of_middle_full_and_pruned_mono
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k+2) (x p) =
      (range (2^(k+2))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < k+2, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(k+2)-2^j)).toNat) = 1)
    (hmid : ∀ (p : ℤ) (a : ℕ), 2^k ≤ a → a < 3*2^k → x p a = true →
      ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x p) i = true)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(k+2) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(k+2)-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true)
    (hpruned : ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2^k → cycle_power_dyadic_b_lift k (x p) b = true →
        cycle_power_dyadic_b_lift k (x p) a = true) ∧
      (∀ a b : ℕ, 2^k ≤ a → a ≤ b → b < 2^(k+1) →
        cycle_power_dyadic_b_lift k (x p) a = true → cycle_power_dyadic_b_lift k (x p) b = true)) :
    ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2^(k+1) → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 2^(k+1) ≤ a → a ≤ b → b < 2^(k+2) → x p a = true → x p b = true) := by
  have hH : 2^(k+1)=2*2^k := by rw [pow_succ]; omega
  have hD : 2^(k+2)=4*2^k := by rw [show k+2=(k+1)+1 by omega, pow_succ, hH]; omega
  apply cycle_power_dyadic_half_monotone_of_middle_full_prune k x htight hexact hmid
  · intro p a b hab hb hx
    have ha : a < 2^k := by omega
    have hh := (hpruned p).1 a b hab hb
      (by simpa only [cycle_power_dyadic_b_lift, if_pos hb] using hx)
    simpa only [cycle_power_dyadic_b_lift, if_pos ha] using hh
  · intro p a b ha₀ hab hbD hx
    have ha' : 2^k ≤ a-2^(k+1) := by omega
    have hab' : a-2^(k+1) ≤ b-2^(k+1) := by omega
    have hb' : b-2^(k+1) < 2^(k+1) := by omega
    have hna : ¬a-2^(k+1) < 2^k := by omega
    have hnb : ¬b-2^(k+1) < 2^k := by omega
    have hea : a-2^(k+1)+2^(k+1) = a := by omega
    have heb : b-2^(k+1)+2^(k+1) = b := by omega
    have hh := (hpruned p).2 (a-2^(k+1)) (b-2^(k+1)) ha' hab' hb'
      (by simpa only [cycle_power_dyadic_b_lift, if_neg hna, hea] using hx)
    simpa only [cycle_power_dyadic_b_lift, if_neg hnb, heb] using hh
  · exact hcover
