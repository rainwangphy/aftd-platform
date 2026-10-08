import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation

/-!
# SocialChoice.FairDivision.Indivisible.rawBestGood

Topic: fair_division   Node: dafd23b13ba2

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.rawBestGood`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/RoundRobin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`rawBestGood w i s hs` is a good in `s` that maximises `w.weight i` over `s`. Defined noncomputably via `Classical.choose` on `Finset.exists_max_image`. Its key properties are `rawBestGood_mem` (membership) and `rawBestGood_le` (maximality).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {n : ℕ} {G : Type*} in
/-- `rawBestGood w i s hs` is a good in `s` that maximises `w.weight i` over `s`. Defined noncomputably via `Classical.choose` on `Finset.exists_max_image`. Its key properties are `rawBestGood_mem` (membership) and `rawBestGood_le` (maximality). -/
noncomputable def SocialChoice.FairDivision.Indivisible.rawBestGood
    (w : AdditiveValuation (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) : G :=
  Classical.choose (Finset.exists_max_image s (w.weight i) hs)
