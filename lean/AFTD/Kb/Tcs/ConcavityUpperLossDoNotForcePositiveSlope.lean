import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace

/-!
# concavity_upper_loss_do_not_force_positive_slope

Topic: quantum   Node: ffc74a57b882

Provenance: helper lemma. Exact certificate for experiment 30130; comparison functions only, related to arXiv:2610.12001 Section 6.

Concavity, monotonicity, the probability range, the threshold value, and an upper loss bound do not by themselves imply a positive loss slope; the constant function is a counterexample. This makes no assertion about a physical strategy.
-/

open Set

theorem concavity_upper_loss_do_not_force_positive_slope
    (β M : ℝ) (hβ : β < 1) (hM : 0 ≤ M) :
    ∃ g : ℝ → ℝ,
      ConcaveOn ℝ (Set.Iic 1) g ∧ AntitoneOn g (Set.Iic 1) ∧ g β = 1 ∧
      (∀ w ≤ 1, 0 ≤ g w ∧ g w ≤ 1) ∧
      (∀ δ, 0 ≤ δ → δ ≤ 1 - β → 1 - g (β + δ) ≤ M * δ) ∧
      (∃ δ, 0 < δ ∧ δ ≤ 1 - β ∧ 1 - g (β + δ) < (9 / 2 : ℝ) * δ) := by
  refine ⟨fun _ => 1, concaveOn_const 1 (convex_Iic 1), ?_, rfl, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp
  · intro w hw
    norm_num
  · intro δ hδ hδR
    simp only [sub_self]
    exact mul_nonneg hM hδ
  · refine ⟨(1 - β) / 2, ?_, ?_, ?_⟩ <;> norm_num <;> linarith
