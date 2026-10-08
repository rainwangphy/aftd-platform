import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation

/-!
# SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation_union

Topic: fair_division   Node: fbf9f99c4eb7

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation_union`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Valuation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Additive valuation of a union of disjoint bundles splits as a sum.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Finset in
variable {N G : Type*} in
/-- Additive valuation of a union of disjoint bundles splits as a sum. -/
lemma SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation_union [DecidableEq G]
    (w : AdditiveValuation N G) (i : N) (S T : Finset G) (h : Disjoint S T) :
    w.toValuation.val i (S ∪ T) = w.toValuation.val i S + w.toValuation.val i T := by
  simp [toValuation, Finset.sum_union h]
