import AFTD.Prelude
import AFTD.Kb.Tcs.OnlineOnlineAlgorithm
import AFTD.Kb.Tcs.OnlineOnlineAlgorithmRun

/-!
# Online.OnlineAlgorithm.run_nil

Topic: online_algorithms   Node: ed4bdbc1c3f9

Provenance: formalization of a published result. Source: EconCSLib, `Online.OnlineAlgorithm.run_nil`. Lean proof by Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Algorithm/Online.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

On no requests, `run` is exactly the end-of-input step.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α σ β : Type*} in
/-- On no requests, `run` is exactly the end-of-input step. -/
@[simp] theorem Online.OnlineAlgorithm.run_nil (alg : OnlineAlgorithm α σ β) (s : σ) :
    alg.run s [] = alg.step s none := rfl
