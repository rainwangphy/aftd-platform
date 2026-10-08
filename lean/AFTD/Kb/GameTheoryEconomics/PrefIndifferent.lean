import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.Indiff
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# Pref.indifferent

Topic: social_choice   Node: d8beb9c66e43

Provenance: formalization of a published result. Source: EconCSLib, `Pref.indifferent`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`p.indiff a b`: outcomes `a` and `b` are indifferent under preference `p`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- `p.indiff a b`: outcomes `a` and `b` are indifferent under preference `p`. -/
def Pref.indifferent {A : Type*} (p : Pref A) (a b : A) : Prop :=
  indiff p a b
