import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena

/-!
# Arena.IsTerminal

Topic: equilibria   Node: 2a51b65c32be

Provenance: formalization of a published result. Source: EconCSLib, `Arena.IsTerminal`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state is terminal if there are no available actions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (A : Arena) in
/-- A state is terminal if there are no available actions. -/
def Arena.IsTerminal (s : A.State) : Prop := IsEmpty (A.Action s)
