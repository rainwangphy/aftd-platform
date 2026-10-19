import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAlphaEf1
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsEF1
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation

/-!
# is_alpha_ef1_one_iff

Topic: fair_division   Node: a44f27fe28fc

Provenance: helper lemma. Sanity lemma for is_alpha_ef1 (arXiv:2610.23686 Definition 1: when α = 1 the allocation is EF1).

1-EF1 is EF1.
-/

theorem is_alpha_ef1_one_iff {N G : Type*} [DecidableEq G]
    (v : SocialChoice.FairDivision.Indivisible.Valuation N G)
    (A : SocialChoice.FairDivision.Indivisible.Allocation N G) :
    is_alpha_ef1 1 v A ↔ SocialChoice.FairDivision.Indivisible.IsEF1 v A := by
  simp [is_alpha_ef1, SocialChoice.FairDivision.Indivisible.IsEF1]
