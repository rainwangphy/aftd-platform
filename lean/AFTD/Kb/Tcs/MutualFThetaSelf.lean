import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFTheta
import AFTD.Kb.Tcs.MutualFInformation

/-!
# mutual_f_theta_self

Topic: information   Node: 2b10d35338e4

Provenance: helper lemma. arXiv:2610.21231 (On the subadditivity of mutual f-information), Appendix B, proof of Theorem 1, eqs. (17)-(18)

Θ_{p_X,p_{Y|X}}(p_X) = Ĩ_f(X;Y) when f(1) = 0 (step (17)-(18) of the proof of Theorem 1 of arXiv:2610.21231).
-/

theorem mutual_f_theta_self {X Y : Type*} [Fintype X] [Fintype Y] (f : ℝ → ℝ) (hf1 : f 1 = 0)
    (pX : X → ℝ) (PY : X → Y → ℝ) (hpX : ∀ x, 0 < pX x) (hsY : ∀ x, ∑ y, PY x y = 1) :
    mutual_f_theta f pX PY pX = mutual_f_information f (fun x y => pX x * PY x y) := by
  unfold mutual_f_theta mutual_f_information
  have h1 : ∀ x, pX x / pX x = 1 := fun x => div_self (hpX x).ne'
  simp only [h1, hf1, mul_zero, Finset.sum_const_zero, sub_zero]
  have hrow : ∀ x, ∑ y, pX x * PY x y = pX x := fun x => by rw [← Finset.mul_sum, hsY, mul_one]
  simp only [hrow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hd : ∀ a b c : ℝ, a / b / c = a / (c * b) := fun a b c => by rw [div_div, mul_comm b c]
  rw [hd]; ring
