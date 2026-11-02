import AFTD.Prelude

/-!
# is_single_high_valuation

Topic: fair_division   Node: 031888b030d8

Provenance: formalization of a published result. Source: arXiv:2610.34625, Sec. 4

An agent's additive valuation vector on m goods is a single-high valuation with ratio R if there exists a good of value R such that all other goods have value 1.
-/

/-- An agent's additive valuation vector on m goods is a single-high valuation with ratio R if there exists a good of value R such that all other goods have value 1. -/
def is_single_high_valuation {m : ℕ} (R : ℝ) (u : Fin m → ℝ) : Prop := ∃ g : Fin m, u g = R ∧ ∀ g' : Fin m, g' ≠ g → u g' = 1
