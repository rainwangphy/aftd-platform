import AFTD.Prelude
import AFTD.Kb.Tcs.Visited
import AFTD.Kb.Tcs.VisitedToFinset

/-!
# Visited.ext

Topic: algorithms   Node: 8c9b5ab690b4

Provenance: formalization of a published result. Source: EconCSLib, `Visited.ext`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Visited.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Visited.ext
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} in
@[ext] theorem Visited.ext {a b : Visited A} (h : a.toFinset = b.toFinset) : a = b := h
