import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op1525_equal_rank_one_gram_sign

Topic: combinatorics   Node: 63200a37d026

Provenance: helper lemma. A component of the complete-multipartite reconstruction route for OP-1525 and arXiv:2611.13901.

Two integer-valued functions with identical pairwise products agree everywhere up to one common global sign.
-/

theorem op1525_equal_rank_one_gram_sign
    {I : Type*} (f g : I → ℤ)
    (h : ∀ i j, f i * f j = g i * g j) :
    f = g ∨ f = fun i => -g i := by
  classical
  by_cases hz : ∀ i, g i = 0
  · left
    funext i
    have hi := h i i
    have hgi := hz i
    nlinarith
  · push_neg at hz
    obtain ⟨k, hk⟩ := hz
    have hs := h k k
    have hk' : f k = g k ∨ f k = -g k := mul_self_eq_mul_self_iff.mp hs
    rcases hk' with heq | heq
    · left
      funext i
      have hi := h i k
      rw [heq] at hi
      exact mul_right_cancel₀ hk hi
    · right
      funext i
      have hi := h i k
      rw [heq] at hi
      have hz' : (f i + g i) * g k = 0 := by nlinarith [hi]
      have := (mul_eq_zero.mp hz').resolve_right hk
      omega
