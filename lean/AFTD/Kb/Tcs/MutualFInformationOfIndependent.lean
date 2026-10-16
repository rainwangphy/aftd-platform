import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFInformation

/-!
# mutual_f_information_of_independent

Topic: information   Node: 81dc77c46a47

Provenance: helper lemma. Sanity lemma for the mutual f-information, arXiv:2610.21231 (On the subadditivity of mutual f-information), Sec. I.

If f(1) = 0 and X, Y are independent (p_{XY}(x, y) = a(x) b(y) with a, b summing to 1), then Ĩ_f(X; Y) = 0.
-/

theorem mutual_f_information_of_independent {X Y : Type*} [Fintype X] [Fintype Y] (f : ℝ → ℝ)
    (hf : f 1 = 0) (a : X → ℝ) (b : Y → ℝ) (ha : ∑ x, a x = 1) (hb : ∑ y, b y = 1) :
    mutual_f_information f (fun x y => a x * b y) = 0 := by
  dsimp [mutual_f_information]
  have h1 : ∀ x, (∑ y', a x * b y') = a x := fun x => by
    rw [← Finset.mul_sum, hb, mul_one]
  have h2 : ∀ y, (∑ x', a x' * b y) = b y := fun y => by
    rw [← Finset.sum_mul, ha, one_mul]
  simp_rw [h1, h2]
  have h3 : ∀ x y, (a x * b y) * f (a x * b y / (a x * b y)) = 0 := fun x y => by
    by_cases hc : a x * b y = 0
    · rw [hc, zero_mul]
    · rw [div_self hc, hf, mul_zero]
  simp_rw [h3]
  simp
