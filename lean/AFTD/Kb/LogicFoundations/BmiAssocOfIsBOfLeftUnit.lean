import AFTD.Prelude
import AFTD.Kb.LogicFoundations.BmiIsBElement

/-!
# bmi_assoc_of_is_b_of_left_unit

Topic: proof_theory   Node: 75385c920adb

Provenance: formalization of a published result. Source: arXiv:2610.37108 Proposition 3.1 -- Finite BM-algebras and fixed-point combinators

Let $(A, \cdot)$ be a magma with a $B$-element $B$. If $B$ is a left unit ($Bx = x$ for all $x$), then the operation is associative: $(xy)z = x(yz)$ for all $x, y, z \in A$.
-/

/-- If B is a B-element and also a left unit in a magma A, then multiplication on A is associative. -/
theorem bmi_assoc_of_is_b_of_left_unit {A : Type*} [Mul A]
    (B : A) (hB : bmi_is_b_element B) (hB_unit : ∀ x : A, B * x = x) :
    ∀ x y z : A, (x * y) * z = x * (y * z) := by
  intro x y z
  have h := hB x y z
  rw [hB_unit x] at h
  exact h
