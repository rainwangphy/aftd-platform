import AFTD.Prelude

/-!
# bmi_is_b_element

Topic: proof_theory   Node: 346f38432807

Provenance: formalization of a published result. Source: arXiv:2610.37108 Definition 0.2(1) -- Finite BM-algebras and fixed-point combinators

An element $B$ in a magma $(A, \cdot)$ is a $B$-element if $((Bx)y)z = x(yz)$ for all $x, y, z \in A$.
-/

/-- An element B of a magma A is a B-element if ((B * x) * y) * z = x * (y * z) for all x, y, z in A. -/
def bmi_is_b_element {A : Type*} [Mul A] (B : A) : Prop := ∀ x y z : A, B * x * y * z = x * (y * z)
