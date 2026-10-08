import AFTD.Prelude
import AFTD.Kb.Tcs.OnlineOnlineAlgorithm
import AFTD.Kb.Tcs.OnlineOnlineAlgorithmRun

/-!
# Online.OnlineAlgorithm.runResult

Topic: online_algorithms   Node: 0e44a22e2b2f

Provenance: formalization of a published result. Source: EconCSLib, `Online.OnlineAlgorithm.runResult`. Lean proof by Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Algorithm/Online.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The **decision** `run` commits to — the second component of `run`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α σ β : Type*} in
/-- The **decision** `run` commits to — the second component of `run`. -/
abbrev Online.OnlineAlgorithm.runResult (alg : OnlineAlgorithm α σ β) (s : σ) (rs : List α) : Option β :=
  (alg.run s rs).2
