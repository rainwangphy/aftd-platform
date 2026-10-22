import AFTD.Prelude

/-!
# IsSpectral

Topic: combinatorics   Node: 5fac8f653031

Provenance: formalization of a published result. Source: arXiv:2610.24022, Section 1 and Equation (2.1)

A subset E of F_2^d is spectral if there is a subset B of F_2^d with |B| = |E| such that for all distinct b, b' in B, the Walsh transform of E at b + b' vanishes.
-/

/-- A subset E of F_2^d is spectral if there exists a spectrum B of size |E| whose characters are pairwise orthogonal on E. -/
def IsSpectral {d : ℕ} (E : Finset (Fin d → ZMod 2)) : Prop := ∃ B : Finset (Fin d → ZMod 2), B.card = E.card ∧
    ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → ∑ e ∈ E, (-1 : ℤ) ^ (dotProduct (b + b') e).val = 0
