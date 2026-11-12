import AFTD.Prelude
import AFTD.Kb.Tcs.HellingerMutualInformation

/-!
# hellinger_mutual_information_of_independent

Topic: information   Node: f3fd9dcb2a0e

Provenance: helper lemma. folklore

For independent finite random variables U and V with product distribution p(u, v) = a(u) * b(v) where marginal distributions a and b each sum to 1, the Hellinger mutual information hellinger_mutual_information (fun u v => a u * b v) is zero.
-/

/-- The Hellinger mutual information of independent random variables is zero. -/
theorem hellinger_mutual_information_of_independent {U V : Type*} [Fintype U] [Fintype V]
    (a : U → ℝ) (b : V → ℝ) (ha : ∑ u, a u = 1) (hb : ∑ v, b v = 1) :
    hellinger_mutual_information (fun u v => a u * b v) = 0 := by
  unfold hellinger_mutual_information
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  have h1 : (∑ v', a u * b v') = a u := by
    rw [← Finset.mul_sum]
    simp [hb]
  have h2 : (∑ u', a u' * b v) = b v := by
    rw [← Finset.sum_mul]
    simp [ha]
  rw [h1, h2, sub_self]
  simp
