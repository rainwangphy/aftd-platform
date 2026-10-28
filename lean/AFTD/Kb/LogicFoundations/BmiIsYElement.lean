import AFTD.Prelude

/-!
# bmi_is_y_element

Topic: proof_theory   Node: 6995deec2b9d

Provenance: formalization of a published result. Source: arXiv:2610.37108 Definition 0.2(4) -- Finite BM-algebras and fixed-point combinators

An element $Y$ in a magma $(A, \cdot)$ is a $Y$-element (fixed-point element) if $Yx = x(Yx)$ for all $x \in A$.
-/

/-- An element Y of a magma A is a Y-element (fixed-point element) if Y * x = x * (Y * x) for all x in A. -/
def bmi_is_y_element {A : Type*} [Mul A] (Y : A) : Prop := ∀ x : A, Y * x = x * (Y * x)
