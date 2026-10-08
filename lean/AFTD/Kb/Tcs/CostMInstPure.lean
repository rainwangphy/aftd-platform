import AFTD.Prelude
import AFTD.Kb.Tcs.CostM
import AFTD.Kb.Tcs.CostMPure

/-!
# CostM.instPure

Topic: algorithms   Node: ccdc7e5999d0

Provenance: formalization of a published result. Source: EconCSLib, `CostM.instPure`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CostM.instPure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {C : Type*} {A B : Type u} in
instance CostM.instPure [Zero C] : Pure (CostM C) := ⟨CostM.pure⟩
