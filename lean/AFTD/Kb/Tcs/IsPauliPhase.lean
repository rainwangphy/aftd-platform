import AFTD.Prelude

/-!
# IsPauliPhase

Topic: quantum   Node: c5b5fcb2ec2a

Provenance: formalization of a published result. Source: arXiv:2610.37807 Definition 2

A complex number $c$ is a Pauli phase if $c \in \{1, -1, i, -i\}$.
-/

/-- A scalar phase is a Pauli phase if it is in {1, -1, i, -i}. -/
def IsPauliPhase (c : ℂ) : Prop := c = 1 ∨ c = -1 ∨ c = Complex.I ∨ c = -Complex.I
