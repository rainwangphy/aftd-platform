import AFTD.Prelude
import AFTD.Kb.Tcs.Visited

/-!
# Visited.ofFinset

Topic: algorithms   Node: b05d4ce3345b

Provenance: formalization of a published result. Source: EconCSLib, `Visited.ofFinset`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Visited.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

View a `Finset A` as a `Visited A`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} in
/-- View a `Finset A` as a `Visited A`. -/
def Visited.ofFinset (s : Finset A) : Visited A := s
