import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# Pref.lt

Topic: social_choice   Node: eed05c029447

Provenance: formalization of a published result. Source: EconCSLib, `Pref.lt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`p.lt a b`: outcome `a` is strictly preferred to `b` under preference `p`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- `p.lt a b`: outcome `a` is strictly preferred to `b` under preference `p`. -/
def Pref.lt {A : Type*} (p : Pref A) (a b : A) : Prop :=
  strict p a b
