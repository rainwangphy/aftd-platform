import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSingleHighValuation

/-!
# is_single_high_profile

Topic: fair_division   Node: 711548b3492c

Provenance: formalization of a published result. Source: arXiv:2610.34625, Sec. 4

A valuation profile of n agents on m goods is a single-high profile with ratio R if every agent has a single-high valuation with ratio R.
-/

/-- A valuation profile of n agents on m goods is a single-high profile with ratio R if every agent has a single-high valuation with ratio R. -/
def is_single_high_profile {n m : ℕ} (R : ℝ) (v : Fin n → Fin m → ℝ) : Prop := ∀ i : Fin n, is_single_high_valuation R (v i)
