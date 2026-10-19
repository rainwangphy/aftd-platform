import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_grundy_val

Topic: combinatorial_games   Node: c6af1907958a

Provenance: formalization of a published result. Source: scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md, Proposition 6.1

The Grundy value spider_grundy_val of the 3-legged spider tree with leg parameters x, y, z : ℕ is defined as spider_gamma (x + y + z + 1) CentreStatus.none [(x, SpiderLegEnd.free), (y, SpiderLegEnd.free), (z, SpiderLegEnd.free)].
-/

/-- Grundy value of the 3-legged spider tree S(x, y, z) in the Game of Arrows. -/
def spider_grundy_val (x y z : ℕ) : ℕ :=
  spider_gamma (x + y + z + 1) .none [(x, .free), (y, .free), (z, .free)]
