import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedVal
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderRhoStar
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd

/-!
# spider_blocked_optionvals

Topic: combinatorial_games   Node: 7297b6bc8798

Provenance: helper lemma. step towards spider_two_leg_blocked_incoming_val

The explicit options list of the state (in;{(r,β),(1,free)}) at fuel r + 2 after substituting the inductive closed forms: for each cut j = 1,…,r-1 of the blocked leg both end conditions contribute rho(r-j;δ,β) xor spider_blocked_val δ (j-1); the end cut j = r contributes only δ = β, namely spider_blocked_val β (r-1); and cutting the free leg of length 1 contributes spider_rho r outward β and spider_rho_star r β, in that order.
-/

/-- Explicit option list of (in;{(r,β),(1,free)}) after substituting the closed forms, in the order the recursion generates it. -/
def spider_blocked_optionvals (r : ℕ) (beta : SpiderLegEnd) : List ℕ := (List.range (r - 1)).flatMap (fun idx =>
    let j := idx + 1
    [SpiderLegEnd.inward, SpiderLegEnd.outward].map
      (fun delta => spider_rho (r - j) delta beta ^^^ spider_blocked_val delta (j - 1)))
  ++ [spider_rho 0 beta beta ^^^ spider_blocked_val beta (r - 1)]
  ++ [spider_rho r SpiderLegEnd.outward beta, spider_rho_star r beta]
