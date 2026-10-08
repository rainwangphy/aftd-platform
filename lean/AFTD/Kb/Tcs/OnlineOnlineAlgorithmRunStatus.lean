import AFTD.Prelude
import AFTD.Kb.Tcs.OnlineOnlineAlgorithm
import AFTD.Kb.Tcs.OnlineOnlineAlgorithmRun

/-!
# Online.OnlineAlgorithm.runStatus

Topic: online_algorithms   Node: d8bc5cbea27c

Provenance: formalization of a published result. Source: EconCSLib, `Online.OnlineAlgorithm.runStatus`. Lean proof by Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Algorithm/Online.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The **terminal status** (state) `run` halts in — the first component of `run`, after the end-of-input step.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α σ β : Type*} in
/-- The **terminal status** (state) `run` halts in — the first component of `run`, after the end-of-input step. -/
abbrev Online.OnlineAlgorithm.runStatus (alg : OnlineAlgorithm α σ β) (s : σ) (rs : List α) : σ :=
  (alg.run s rs).1
