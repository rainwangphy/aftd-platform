import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena

/-!
# Arena.Reachable

Topic: equilibria   Node: 7ebe799f6a79

Provenance: formalization of a published result. Source: EconCSLib, `Arena.Reachable`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Reachability.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state `t` is reachable from `s` if a finite legal path leads from `s` to `t`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A state `t` is reachable from `s` if a finite legal path leads from `s` to `t`. -/
inductive Arena.Reachable (A : Arena) : A.State → A.State → Prop where
  | refl (s : A.State) : A.Reachable s s
  | step {s t : A.State} (a : A.Action s)
      (h : A.Reachable (A.next s a) t) :
      A.Reachable s t
