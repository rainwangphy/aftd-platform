import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEightBlockExtensionAt
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassPrune
import AFTD.Kb.Tcs.CyclePowerDyadicPruneExact
import AFTD.Kb.Tcs.CyclePowerDyadicPruneCover
import AFTD.Kb.Tcs.CyclePowerDyadicExactEndpoints

/-!
# cycle_power_dyadic_outer_quarter_monotone_of_eight_block_extension

Topic: combinatorics   Node: b3b3fd86b655

Provenance: helper lemma. Uniform local structural route for OP-205 / RT-1, following arXiv:2610.15635. The Boolean eight-block extension remains conjectured; the induction result keeps it as an explicit hypothesis. Finite guarded computations are evidence only, and no graph covering value or research advance is claimed.

Assuming the local eight-block extension predicate at every positive block size, every tight exact fully ordinarily covered dyadic model has initial first quarters and terminal last quarters. The extension principle is an explicit unproved hypothesis, so this is a conditional reduction of target I.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_outer_quarter_monotone_of_eight_block_extension
    (hstep : ∀ q : ℕ, 0 < q → cycle_power_eight_block_extension_at q)
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k+2) (x p) =
      (range (2^(k+2))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < k+2, ∀ v : ℤ, (range (2^j)).sum (fun a =>
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
    let q := 2^k
    have hq : 0 < q := Nat.two_pow_pos _
    have hP₁ : 2^(k+1)=2*q := by dsimp [q]; rw [pow_succ]; omega
    have hP₂ : 2^(k+2)=4*q := by rw [show k+2=(k+1)+1 by omega,pow_succ,hP₁]; omega
    have hP₃ : 2^(k+3)=8*q := by rw [show k+3=(k+2)+1 by omega,pow_succ,hP₂]; omega
    have ht : ∀ p, cycle_power_dyadic_class_weight (k+3) (x p) =
      (range (2^(k+3))).sum (fun a => (x p a).toNat) := htight
    have he : ∀ j < k+3, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(k+3)-2^j)).toNat) = 1 := hexact
    have hc : ∀ d : ℕ, 1 ≤ d → d < 2^(k+3) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(k+3)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true := hcover
    let y : ℤ → ℕ → Bool := fun p => cycle_power_dyadic_b_lift (k+1) (x p)
    have hyT := fun p => cycle_power_dyadic_tight_class_prune (k+1) (x p) (ht p)
    have hyE := cycle_power_dyadic_prune_exact (k+1) x he
    have hyC := cycle_power_dyadic_prune_cover (k+1) x ht hc
    have hy := ih y hyT hyE hyC
    have hs := hstep q hq x
    have hends : ∀ p, x p 0 = true ∧ x p (8*q-1) = true := by
      simpa only [hP₃] using cycle_power_dyadic_exact_endpoints (k+3) (by omega) x he
    have hp4 : ∀ p a, a < 4*q →
        (a < 2*q → x p (a+4*q) = true → x p a = true) ∧
        (2*q ≤ a → x p a = true → x p (a+4*q) = true) := by
      intro p a ha
      have hh := cycle_power_dyadic_tight_class_parent (k+3) (k+2)
        (by omega) (by omega) (x p) (ht p) a (by simpa only [hP₂] using ha)
      have hp : 2^(k+2-1)=2*q := by simpa only [show k+2-1=k+1 by omega] using hP₁
      have hi : a+8*q-4*q=a+4*q := by omega
      simpa only [hp,hP₃,hP₂,hi] using hh
    have hp6 : ∀ p a, a < 2*q →
        (a < q → x p (a+6*q) = true → x p a = true) ∧
        (q ≤ a → x p a = true → x p (a+6*q) = true) := by
      intro p a ha
      have hh := cycle_power_dyadic_tight_class_parent (k+3) (k+1)
        (by omega) (by omega) (x p) (ht p) a (by simpa only [hP₁] using ha)
      have hp : 2^(k+1-1)=q := by simp only [Nat.add_sub_cancel]; rfl
      have hi : a+8*q-2*q=a+6*q := by omega
      simpa only [hp,hP₃,hP₁,hi] using hh
    have hEx : ∀ L : ℕ, (L=q ∨ L=2*q ∨ L=4*q) → ∀ v : ℤ,
        (range L).sum (fun a =>
          (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+8*q-L)).toNat) = 1 := by
      intro L hL v
      rcases hL with rfl | rfl | rfl
      · simpa only [hP₃] using he k (by omega) v
      · simpa only [hP₃,hP₁] using he (k+1) (by omega) v
      · simpa only [hP₃,hP₂] using he (k+2) (by omega) v
    have hOut : ∀ p : ℤ,
        (∀ a b : ℕ, a ≤ b → b < q → x p b = true → x p a = true) ∧
        (∀ a b : ℕ, 7*q ≤ a → a ≤ b → b < 8*q →
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
        have ha' : y p (a-4*q) = true := by
          dsimp [y,cycle_power_dyadic_b_lift]
          rw [if_neg (by omega)]
          convert hx using 1 <;> congr 1 <;> omega
        have hb' := (hy p).2 (a-4*q) (b-4*q) (by dsimp [q] at *; omega)
          (by omega) (by omega) ha'
        dsimp [y,cycle_power_dyadic_b_lift] at hb'
        rw [if_neg (by omega)] at hb'
        convert hb' using 1 <;> congr 1 <;> omega
    have hCov : ∀ d : ℕ, 1 ≤ d → d < 8*q → ∀ v : ℤ,
        ∃ a : ℕ, a < 8*q-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true := by simpa only [hP₃] using hc
    have hres := hs hends hp4 hp6 hEx hOut hCov
    have hLast : 3*2^(k+1)=6*q := by rw [hP₁]; omega
    have hLast' : 3*(2*q)=6*q := by omega
    simpa only [Nat.succ_eq_add_one,show k+1+2=k+3 by omega,hP₁,hP₃,hLast'] using hres
