import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd

/-!
# spider_none_one_inward_one_outward_opts

Topic: combinatorial_games   Node: f9163356dfa7

Provenance: helper lemma. step towards spider_blocked_none_one_inward_one_outward

The explicit closed-form option list of the state (none;{(1,inward),(1,outward),(r,φ)}) after substituting the sub-state values: the two short-leg options (each r xor 1), the two j = 1 options of the long leg (the pair {0,1} given by spider_rho (r-1) delta φ), the block of options from the cuts j = 2..r-1 of the long leg (rho(r-j) xor (j-1), reindexed with i = j-2), and the last cut j = r, which contributes r-1.
-/

/-- The closed-form option list of the κ₁ blocked family after substituting all sub-state values. -/
def spider_none_one_inward_one_outward_opts (r : ℕ) (φ : SpiderLegEnd) : List ℕ := [r ^^^ 1, r ^^^ 1,
      spider_rho (r - 1) SpiderLegEnd.inward φ,
      spider_rho (r - 1) SpiderLegEnd.outward φ] ++
    (List.range (r - 2)).flatMap (fun i =>
      [spider_rho (r - 2 - i) SpiderLegEnd.inward φ ^^^ (i + 1),
       spider_rho (r - 2 - i) SpiderLegEnd.outward φ ^^^ (i + 1)]) ++
    [r - 1]
