import AFTD.Prelude
import AFTD.Kb.Tcs.OnlineOnlineAlgorithm
import AFTD.Kb.Tcs.OnlineOnlineAlgorithmRun
import AFTD.Kb.Tcs.OnlineOnlineAlgorithmRunCons
import AFTD.Kb.Tcs.OnlineOnlineAlgorithmRunNil
import AFTD.Kb.Tcs.OnlineOnlineAlgorithmRunConsSome

/-!
# Online.OnlineAlgorithm.run_cons_none

Topic: online_algorithms   Node: 88b68d2d0e70

Provenance: formalization of a published result. Source: EconCSLib, `Online.OnlineAlgorithm.run_cons_none`. Lean proof by Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Algorithm/Online.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If the step on `r` defers (`none`), the run continues on `rs`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Online Online.OnlineAlgorithm in
variable {α σ β : Type*} in
/-- If the step on `r` defers (`none`), the run continues on `rs`. -/
@[simp] theorem Online.OnlineAlgorithm.run_cons_none (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', none)) :
    alg.run s (r :: rs) = alg.run s' rs := by
  rw [run_cons, h]
