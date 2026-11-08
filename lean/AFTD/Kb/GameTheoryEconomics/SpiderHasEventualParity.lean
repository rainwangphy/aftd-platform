import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGrundyVal

/-!
# spider_has_eventual_parity

Topic: combinatorial_games   Node: f1a4495f147f

Provenance: formalization of a published result. Source: arXiv:2610.15145, Conjecture 7.4

A pair of positive integers (x, y) has eventual parity if there exists a natural number z₀ such that for all natural numbers z with z₀ ≤ z, the Grundy value spider_grundy_val x y z of the 3-legged spider tree S(x, y, z) is equal to z % 2.
-/

/-- A pair of spider leg lengths (x, y) has eventual parity if the Grundy values of S(x, y, z) eventually equal z mod 2. -/
def spider_has_eventual_parity (x y : ℕ) : Prop := ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z → spider_grundy_val x y z = z % 2
