import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StrictlyPreferred

/-!
# StrictlyPreferred.irrefl

Topic: social_choice   Node: 1244bd608b8a

Provenance: formalization of a published result. Source: EconCSLib, `StrictlyPreferred.irrefl`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Strict preference is irreflexive. [MSZ Ex 2.1(a)]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} [Preorder A] in
/-- Strict preference is irreflexive. [MSZ Ex 2.1(a)] -/
theorem StrictlyPreferred.irrefl (a : A) : ¬ StrictlyPreferred a a :=
  lt_irrefl a
