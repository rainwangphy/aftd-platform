import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderUpdateCentre
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderRho

/-!
# spider_blocked_raw_opts

Topic: combinatorial_games   Node: 8f81821d5ffd

Provenance: helper lemma. step towards op211_three_legged_spider_eventual_parity

The raw option list of the state (in;{(r,β),(1,free)}) after exactly one unfolding step of spider_gamma at fuel r+2, with the *sub-state Grundy values left unevaluated*: the zipIdx.flatMap over the two legs, each cut j = 1,…,h, both directions δ, skipping the prohibited end cut, and dispatching j ≥ 2 to the two-leg sub-state ((j-1,δ) :: rest) and j = 1 to the one-leg rest.
-/

/-- The one-unfolding option list of (in;{(r,β),(1,free)}) at fuel r+2, with sub-state values kept unevaluated. -/
def spider_blocked_raw_opts (r : ℕ) (beta : SpiderLegEnd) : List ℕ := ([(r, beta), (1, SpiderLegEnd.free)] : List (ℕ × SpiderLegEnd)).zipIdx.flatMap
    (fun ⟨⟨h, phi⟩, idx⟩ =>
      let rest := ([(r, beta), (1, SpiderLegEnd.free)] : List (ℕ × SpiderLegEnd)).eraseIdx idx
      (List.range h).flatMap (fun j_zero =>
        let j := j_zero + 1
        [SpiderLegEnd.inward, SpiderLegEnd.outward].filterMap (fun delta =>
          if j == h ∧ phi ≠ SpiderLegEnd.free ∧ delta ≠ phi then none
          else
            let d := spider_rho (h - j) delta phi
            if j ≥ 2 then
              some (d ^^^ spider_gamma (r + 1) CentreStatus.incoming ((j - 1, delta) :: rest))
            else
              some (d ^^^ spider_gamma (r + 1)
                (spider_update_centre CentreStatus.incoming delta) rest))))
