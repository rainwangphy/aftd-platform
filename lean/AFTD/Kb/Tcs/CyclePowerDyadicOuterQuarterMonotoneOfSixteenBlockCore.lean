import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerSixteenBlockOuterQuartersOfUpperVertical
import AFTD.Kb.Tcs.CyclePowerDyadicSixteenBlockGeometry
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassPrune
import AFTD.Kb.Tcs.CyclePowerDyadicPruneExact
import AFTD.Kb.Tcs.CyclePowerDyadicPruneCover
import AFTD.Kb.Tcs.CyclePowerDyadicExactEndpoints
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.Tcs.CyclePowerSixteenBlockNoVerticalOverlap

/-!
# cycle_power_dyadic_outer_quarter_monotone_of_sixteen_block_core

Topic: combinatorics   Node: 3dcadd8877b5

Provenance: helper lemma. Uniform structural route for OP-205 / RT-1, following arXiv:2610.15635. These are helper reductions, not a proof of the open covering value and not a research advance. The upper-vertical core remains an explicit unproved hypothesis.

Conditional on upper-vertical exclusion only at dyadic block sizes h=2^j, every tight all-rank-exact fully ordinarily covered dyadic model has monotone outer quarters. This supplies a uniform induction from the stronger sixteen-block local core; that core is explicitly assumed, and neither the generic two-parent extension nor count preservation is proved.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_dyadic_outer_quarter_monotone_of_sixteen_block_core
    (hstep : ∀ (j : ℕ) (y : ℤ → ℕ → Bool), CyclePowerSixteenBlock.Geometry (2^j) y →
      (∀ v : ℤ, (Finset.range (8*2^j)).sum (fun a =>
        (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+8*2^j)).toNat) = 1) →
      ∀ p t, 2^j ≤ t → t < 2*2^j → y p (2*2^j+t) = true → y p t = true)
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k+2) (x p) =
      (Finset.range (2^(k+2))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < k+2, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(k+2)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(k+2) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(k+2)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true) :
    ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2^k → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 3*2^k ≤ a → a ≤ b → b < 2^(k+2) →
        x p a = true → x p b = true) := by
  induction k generalizing x with
  | zero =>
    intro p
    constructor
    · intro a b hab hb hx
      have he : a=b := by norm_num at hb; omega
      rwa [he]
    · intro a b ha hab hb hx
      have he : a=b := by norm_num at ha hb; omega
      rwa [← he]
  | succ k ih =>
    by_cases hk : k=0
    · subst k
      have hends := cycle_power_dyadic_exact_endpoints 3 (by omega) x hexact
      intro p
      constructor
      · intro a b hab hb hx
        by_cases he : a=b
        · rwa [he]
        · have he : a=0 := by norm_num at hb; omega
          simpa only [he] using (hends p).1
      · intro a b ha hab hb hx
        by_cases he : a=b
        · rwa [← he]
        · have he : b=7 := by norm_num at ha hb; omega
          simpa only [he,show 2^3-1=7 by norm_num] using (hends p).2
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      let h := 2^j
      have hp : 0 < h := Nat.two_pow_pos j
      have h1 : 2^(j+1)=2*h := by dsimp [h]; rw [pow_succ]; omega
      have h2 : 2^(j+2)=4*h := by rw [show j+2=(j+1)+1 by omega,pow_succ,h1]; omega
      have h3 : 2^(j+3)=8*h := by rw [show j+3=(j+2)+1 by omega,pow_succ,h2]; omega
      have h4 : 2^(j+4)=16*h := by rw [show j+4=(j+3)+1 by omega,pow_succ,h3]; omega
      have ht : ∀ p, cycle_power_dyadic_class_weight (j+4) (x p) =
          (Finset.range (2^(j+4))).sum (fun a => (x p a).toNat) := htight
      have he : ∀ i < j+4, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
          (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(j+4)-2^i)).toNat) = 1 := hexact
      have hc : ∀ d : ℕ, 1 ≤ d → d < 2^(j+4) → ∀ v : ℤ,
          ∃ a : ℕ, a < 2^(j+4)-d ∧ x (v-(a : ℤ)) a = true ∧
            x (v-(a : ℤ)) (a+d) = true := hcover
      let y : ℤ → ℕ → Bool := fun p => cycle_power_dyadic_b_lift (j+2) (x p)
      have hyT := fun p => cycle_power_dyadic_tight_class_prune (j+2) (x p) (ht p)
      have hyE := cycle_power_dyadic_prune_exact (j+2) x he
      have hyC := cycle_power_dyadic_prune_cover (j+2) x ht hc
      have hy : ∀ p : ℤ,
          (∀ a b : ℕ, a ≤ b → b < 2^(j+1) → y p b = true → y p a = true) ∧
          (∀ a b : ℕ, 3*2^(j+1) ≤ a → a ≤ b → b < 2^(j+3) →
            y p a = true → y p b = true) := ih y hyT hyE hyC
      have hout : ∀ p : ℤ,
          (∀ a b : ℕ, a ≤ b → b < 2^(j+1) → x p b = true → x p a = true) ∧
          (∀ a b : ℕ, 7*2^(j+1) ≤ a → a ≤ b → b < 2^(j+4) →
            x p a = true → x p b = true) := by
        intro p
        constructor
        · intro a b hab hb hx
          have hb' : y p b = true := by
            dsimp [y,cycle_power_dyadic_b_lift]
            rw [if_pos (by omega)]
            exact hx
          have ha' := (hy p).1 a b hab hb hb'
          dsimp [y,cycle_power_dyadic_b_lift] at ha'
          rwa [if_pos (by omega)] at ha'
        · intro a b ha hab hb hx
          have ha' : y p (a-8*h) = true := by
            dsimp [y,cycle_power_dyadic_b_lift]
            rw [if_neg (by omega)]
            convert hx using 1 <;> congr 1 <;> omega
          have hb' := (hy p).2 (a-8*h) (b-8*h) (by omega) (by omega) (by omega) ha'
          dsimp [y,cycle_power_dyadic_b_lift] at hb'
          rw [if_neg (by omega)] at hb'
          convert hb' using 1 <;> congr 1 <;> omega
      have M := cycle_power_dyadic_sixteen_block_geometry j x ht he hc hout
      have he4 : ∀ v : ℤ, (Finset.range (8*h)).sum (fun a =>
          (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+8*h)).toNat) = 1 := by
        intro v
        have hi (a : ℕ) : a+16*h-8*h=a+8*h := by omega
        simpa only [h3,h4,hi] using he (j+3) (by omega) v
      have hs := cycle_power_sixteen_block_outer_quarters_of_upper_vertical h x M he4 (hstep j)
      have hr : 3*(4*h)=12*h := by omega
      simpa only [Nat.succ_eq_add_one,show j+1+1=j+2 by omega,
        show j+2+2=j+4 by omega,h2,h4,hr] using hs
