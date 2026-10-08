import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleRawBestGood
import AFTD.Kb.Tcs.Weight

/-!
# SocialChoice.FairDivision.Indivisible.rawBestGood_mem

Topic: fair_division   Node: 31b51d251658

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.rawBestGood_mem`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/RoundRobin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`rawBestGood` lies in the candidate set `s`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {n : ℕ} {G : Type*} in
/-- `rawBestGood` lies in the candidate set `s`. -/
lemma SocialChoice.FairDivision.Indivisible.rawBestGood_mem
    (w : AdditiveValuation (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) :
    rawBestGood w i s hs ∈ s :=
  (Classical.choose_spec (Finset.exists_max_image s (w.weight i) hs)).1
