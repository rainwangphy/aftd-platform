import AFTD.Prelude
import AFTD.Kb.LogicFoundations.BmiIsMElement
import AFTD.Kb.LogicFoundations.BmiIsIElement

/-!
# bmi_idempotent_of_assoc_of_is_m_of_is_i

Topic: proof_theory   Node: d63e5992a13f

Provenance: formalization of a published result. Source: arXiv:2610.37108 Theorem 3.3 -- Finite BM-algebras and fixed-point combinators

Let $(A, \cdot)$ be an associative magma with an $M$-element $M$ and an $I$-element $I$. Then every element $x \in A$ is idempotent: $xx = x$.
-/

/-- In any associative magma with an M-element and an I-element, every element is idempotent. -/
theorem bmi_idempotent_of_assoc_of_is_m_of_is_i {A : Type*} [Mul A]
    (h_assoc : ∀ x y z : A, (x * y) * z = x * (y * z))
    (M I : A) (hM : bmi_is_m_element M) (hI : bmi_is_i_element I) :
    ∀ x : A, x * x = x := by
  intro x
  calc x * x = M * x := (hM x).symm
    _ = M * (I * x) := by rw [hI x]
    _ = (M * I) * x := (h_assoc M I x).symm
    _ = (I * I) * x := by rw [hM I]
    _ = I * (I * x) := h_assoc I I x
    _ = I * x := hI (I * x)
    _ = x := hI x
