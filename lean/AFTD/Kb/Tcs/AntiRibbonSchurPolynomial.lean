import AFTD.Prelude
import AFTD.Kb.Tcs.SchurPolynomial
import AFTD.Kb.Tcs.AntiRibbonDiagram

/-!
# anti_ribbon_schur_polynomial

Topic: combinatorics   Node: 921c3628dcfd

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 5.1

For a positive integer N : ℕ, a descent set S : Finset ℕ, and a bound m : ℕ, the anti-ribbon Schur polynomial anti_ribbon_schur_polynomial N S m is the Schur polynomial of the anti-ribbon diagram anti_ribbon_diagram N S in m variables.
-/

/-- Anti-ribbon Schur polynomial associated with descent set S and size N in m variables. -/
noncomputable def anti_ribbon_schur_polynomial (N : ℕ) (S : Finset ℕ) (m : ℕ) : MvPolynomial ℕ ℤ := schur_polynomial (anti_ribbon_diagram N S) m
