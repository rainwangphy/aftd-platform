import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleRawBestGood

/-!
# SocialChoice.FairDivision.Indivisible.rawBestGood_le

Topic: fair_division   Node: 715cfebd07e8

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.rawBestGood_le`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/RoundRobin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every element of `s` is no more valuable (to agent `i`) than `rawBestGood`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {n : ℕ} {G : Type*} in
/-- Every element of `s` is no more valuable (to agent `i`) than `rawBestGood`. -/
lemma SocialChoice.FairDivision.Indivisible.rawBestGood_le
    (w : AdditiveValuation (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) {g : G} (hg : g ∈ s) :
    w.weight i g ≤ w.weight i (rawBestGood w i s hs) :=
  (Classical.choose_spec (Finset.exists_max_image s (w.weight i) hs)).2 g hg
