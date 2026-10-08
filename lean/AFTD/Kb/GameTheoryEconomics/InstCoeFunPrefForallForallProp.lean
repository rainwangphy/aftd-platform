import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pref

/-!
# instCoeFunPrefForallForallProp

Topic: social_choice   Node: 8198aaffe814

Provenance: formalization of a published result. Source: EconCSLib, `instCoeFunPrefForallForallProp`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

instCoeFunPrefForallForallProp
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance instCoeFunPrefForallForallProp : CoeFun (Pref A) (fun _ => A → A → Prop) where
  coe p := p.rel
