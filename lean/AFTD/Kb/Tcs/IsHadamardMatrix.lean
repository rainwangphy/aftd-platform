import AFTD.Prelude

/-!
# IsHadamardMatrix

Topic: combinatorics   Node: 7ea4b8521597

Provenance: formalization of a published result. Source: arXiv:2610.27175 (Recent progress in the construction of Hadamard matrices), Section 1 (definition of a Hadamard matrix)

A square integer matrix H indexed by a finite type of size n is a Hadamard matrix when every entry is 1 or -1 and H Hᵀ = n I.
-/

/-- A square integer matrix H indexed by a finite type of size n is a Hadamard matrix when every entry is 1 or -1 and H Hᵀ = n I. -/
def IsHadamardMatrix {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℤ) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧ H * H.transpose = (Fintype.card n : ℤ) • (1 : Matrix n n ℤ)
