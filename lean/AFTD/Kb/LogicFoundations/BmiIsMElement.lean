import AFTD.Prelude

/-!
# bmi_is_m_element

Topic: proof_theory   Node: 9e4f540ef026

Provenance: formalization of a published result. Source: arXiv:2610.37108 Definition 0.2(2) -- Finite BM-algebras and fixed-point combinators

An element $M$ in a magma $(A, \cdot)$ is an $M$-element if $Mx = xx$ for all $x \in A$ .
-/

/-- An element M of a magma A is an M-element if M * x = x * x for all x in A. -/
def bmi_is_m_element {A : Type*} [Mul A] (M : A) : Prop := ∀ x : A, M * x = x * x
