import AFTD.Prelude

/-!
# condorcet_edge_circulation_dual_bound

Topic: social_choice   Node: 03ee03177296

Provenance: helper lemma. IN-380, OP-19 campaign session 8, 2026-10-30. Self-contained helper for the strict-half acyclic-separation route. The general unrestricted one-child equality was refuted in IN-372; this work repairs only the strict-half existence reduction. Standard finite matching, rational density, and circulation weak duality are used. No new election bound or research novelty is claimed. See lean/AFTD/Scratch/In380Oct30/HalfThresholdDerivation.txt.

Given nonnegative real edge weights supported on a finite directed relation, with equal incoming and outgoing sums at each vertex, any real vertex functions p and h satisfying t+h(b) <= p(a)+h(a) on every arrow obey t times total edge weight <= the sum over vertices of outgoing weight times p. No acyclicity, S3, or normalization is assumed.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_edge_circulation_dual_bound
    (m : ℕ) (R : Fin m → Fin m → Prop)
    (f : Fin m → Fin m → ℝ) (p h : Fin m → ℝ) (t : ℝ)
    (hf : ∀ a b, 0 ≤ f a b)
    (hsupport : ∀ a b, ¬ R a b → f a b = 0)
    (hbalance : ∀ a, ∑ b, f a b = ∑ b, f b a)
    (hlocal : ∀ a b, R a b → t + h b ≤ p a + h a) :
    t * (∑ a, ∑ b, f a b) ≤ ∑ a, (∑ b, f a b) * p a := by
  have hsum : (∑ a, ∑ b, f a b * (t + h b)) ≤
      ∑ a, ∑ b, f a b * (p a + h a) := by
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro b hb
    by_cases hab : R a b
    · exact mul_le_mul_of_nonneg_left (hlocal a b hab) (hf a b)
    · simp [hsupport a b hab]
  have hcancel : (∑ a, ∑ b, f a b * h b) =
      ∑ a, (∑ b, f a b) * h a := by
    rw [sum_comm]
    simp_rw [← sum_mul,← hbalance]
  have hleft : (∑ a, ∑ b, f a b * (t + h b)) =
      t * (∑ a, ∑ b, f a b) + ∑ a, (∑ b, f a b) * h a := by
    simp_rw [mul_add,sum_add_distrib]
    rw [hcancel]
    simp only [← sum_mul,mul_comm t]
  have hright : (∑ a, ∑ b, f a b * (p a + h a)) =
      (∑ a, (∑ b, f a b) * p a) + ∑ a, (∑ b, f a b) * h a := by
    simp_rw [← sum_mul,mul_add,sum_add_distrib]
  rw [hleft,hright] at hsum
  linarith
