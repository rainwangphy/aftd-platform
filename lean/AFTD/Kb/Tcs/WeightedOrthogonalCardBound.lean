import AFTD.Prelude

/-!
# weighted_orthogonal_card_bound

Topic: combinatorics   Node: 8f252966a683

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

A finite family of vectors with nonzero weighted squared norms and zero off-diagonal weighted pair products has size at most its ambient coordinate type. The weights and vectors are rational.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem weighted_orthogonal_card_bound {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℚ) (v : J → I → ℚ)
    (horth : ∀ a b, a ≠ b → (∑ i, w i * v a i * v b i) = 0)
    (hnorm : ∀ a, (∑ i, w i * v a i * v a i) ≠ 0) :
    Fintype.card J ≤ Fintype.card I := by
  classical
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have he := congrArg (fun f : I → ℚ => ∑ i, w i * f i * v a i) hg
    have heq : (∑ i, w i * (∑ j, g j • v j) i * v a i) =
        ∑ j, g j * (∑ i, w i * v j i * v a i) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_sum, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intro i hi
      ring
    rw [heq] at he
    simp only [Pi.zero_apply, mul_zero, zero_mul, sum_const_zero] at he
    have hs : (∑ j, g j * (∑ i, w i * v j i * v a i)) =
        g a * (∑ i, w i * v a i * v a i) := by
      apply sum_eq_single a
      · intro j hj hja
        rw [horth j a hja, mul_zero]
      · simp
    rw [hs] at he
    exact (mul_eq_zero.mp he).resolve_right (hnorm a)
  exact (Pi.basisFun ℚ I).card_le_card_of_linearIndependent hli
