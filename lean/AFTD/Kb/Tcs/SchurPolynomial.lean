import AFTD.Prelude
import AFTD.Kb.Tcs.SsytBounded
import AFTD.Kb.Tcs.TableauWeight

/-!
# schur_polynomial

Topic: combinatorics   Node: 79820a6c7567

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 5.1

For a finite diagram D : Finset (ℕ × ℕ) and a positive integer m : ℕ, the Schur polynomial schur_polynomial D m in MvPolynomial ℕ ℤ is the sum of the monomial weights tableau_weight D M over all semi-standard Young tableaux M in ssyt_bounded D m.
-/

open scoped BigOperators in
/-- Schur polynomial associated with diagram D in m variables. -/
noncomputable def schur_polynomial (D : Finset (ℕ × ℕ)) (m : ℕ) : MvPolynomial ℕ ℤ := ∑ M ∈ ssyt_bounded D m, tableau_weight D M
