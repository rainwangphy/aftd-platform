import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena

/-!
# Arena.ofFin

Topic: equilibria   Node: 9cff8e9173f1

Provenance: formalization of a published result. Source: EconCSLib, `Arena.ofFin`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Build an arena from a `Fin`-indexed state space with finite action types. Terminal states have `nActions s = 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Build an arena from a `Fin`-indexed state space with finite action types. Terminal states have `nActions s = 0`. -/
def Arena.ofFin (n : ℕ) (nActions : Fin n → ℕ)
    (next : (s : Fin n) → Fin (nActions s) → Fin n) : Arena where
  State := Fin n
  Action := fun s => Fin (nActions s)
  next := next
