import AFTD.Prelude
import AFTD.Kb.LogicFoundations.BmiIsMElement

/-!
# bmi_is_left_unit_m_of_is_m_of_idempotent

Topic: proof_theory   Node: 3dea955672c5

Provenance: helper lemma. arXiv:2610.37108 Theorem 3.3

Let $(A, \cdot)$ be an idempotent magma (satisfying $x \cdot x = x$ for all $x \in A$) equipped with an $M$-element $M$ (satisfying $M \cdot x = x \cdot x$ for all $x \in A$). Then $M$ is a left unit: $M \cdot x = x$ for all $x \in A$.
-/

/-- An M-element in an idempotent magma is a left unit. -/
theorem bmi_is_left_unit_m_of_is_m_of_idempotent {A : Type*} [Mul A]
    (M : A) (hM : bmi_is_m_element M) (hidem : ∀ x : A, x * x = x) :
    ∀ x : A, M * x = x := by
  intro x
  rw [hM x, hidem x]
