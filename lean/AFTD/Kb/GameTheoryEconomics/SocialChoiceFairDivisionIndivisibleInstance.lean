import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionInstance

/-!
# SocialChoice.FairDivision.Indivisible.Instance

Topic: fair_division   Node: c0942414319b

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.Instance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An ordinal indivisible-goods instance. `allGoods` is the finite set of goods to allocate. Each agent ranks bundles of goods, represented as `Finset G`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- An ordinal indivisible-goods instance. `allGoods` is the finite set of goods to allocate. Each agent ranks bundles of goods, represented as `Finset G`. -/
structure SocialChoice.FairDivision.Indivisible.Instance (N G : Type*) where
  /-- The goods that must be allocated. -/
  allGoods : Finset G
  /-- Each agent's ordinal preference over bundles. -/
  sharePref : N → Pref (Finset G)
