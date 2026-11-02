import AFTD.Prelude

/-!
# is_povm

Topic: quantum   Node: 034f4fe5028b

Provenance: formalization of a published result. Source: Standard definition (positive-operator-valued measure), as used in arXiv:2610.12001 (Exact value and rigidity of the 2x3 magic rectangle), Sec. 2.

A finite family of complex d×d matrices indexed by a finite outcome set is a POVM (positive-operator-valued measure): each effect is positive semidefinite and the effects sum to the identity matrix.
-/

/-- A finite family of complex `d × d` matrices is a POVM: every effect is positive semidefinite and the effects sum to the identity. -/
def is_povm {ι : Type} [Fintype ι] (d : ℕ) (E : ι → Matrix (Fin d) (Fin d) ℂ) : Prop := open scoped ComplexOrder in (∀ i, (E i).PosSemidef) ∧ ∑ i, E i = 1
