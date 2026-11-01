import AFTD.Prelude

/-!
# is_dichotomic_observable

Topic: quantum   Node: 12daa6df6662

Provenance: formalization of a published result. Source: arXiv:2610.35838 Sec. II.3

A dichotomic projective observable B on a complex Hilbert space satisfies B* = B and B^2 = I.
-/

/-- A dichotomic projective observable on a Hilbert space is a self-adjoint operator with square equal to the identity. -/
def is_dichotomic_observable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (B : E →L[ℂ] E) : Prop := IsSelfAdjoint B ∧ B ^ 2 = 1
