import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGrundyVal

/-!
# spider_grundy_val_one_one_one

Topic: combinatorial_games   Node: fb9886fed0ce

Provenance: formalization of a published result. Source: arXiv:2610.15145, Table 4

The Grundy value of the spider tree S(1, 1, 1) satisfies spider_grundy_val 1 1 1 = 1.
-/

/-- Grundy value of the symmetric spider S(1, 1, 1) is 1. -/
theorem spider_grundy_val_one_one_one : spider_grundy_val 1 1 1 = 1 := by first | (simp_all; done) | omega | decide | linarith | positivity | (aesop; done)
