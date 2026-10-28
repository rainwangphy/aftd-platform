import AFTD.Prelude

/-!
# bmi_is_i_element

Topic: proof_theory   Node: 6d383b5aa3c9

Provenance: formalization of a published result. Source: arXiv:2610.37108 Definition 0.2(3) -- Finite BM-algebras and fixed-point combinators

An element $I$ in a magma $(A, \cdot)$ is an $I$-element (a left unit) if $Ix = x$ for all $x \in A$.
-/

/-- An element I of a magma A is an I-element (left unit) if I * x = x for all x in A. -/
def bmi_is_i_element {A : Type*} [Mul A] (I : A) : Prop := ∀ x : A, I * x = x
