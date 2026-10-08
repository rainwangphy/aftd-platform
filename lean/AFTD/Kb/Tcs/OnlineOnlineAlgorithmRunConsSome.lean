import AFTD.Prelude
import AFTD.Kb.Tcs.OnlineOnlineAlgorithm
import AFTD.Kb.Tcs.OnlineOnlineAlgorithmRun
import AFTD.Kb.Tcs.OnlineOnlineAlgorithmRunCons
import AFTD.Kb.Tcs.OnlineOnlineAlgorithmRunNil

/-!
# Online.OnlineAlgorithm.run_cons_some

Topic: online_algorithms   Node: 98e4d38b1403

Provenance: formalization of a published result. Source: EconCSLib, `Online.OnlineAlgorithm.run_cons_some`. Lean proof by Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Algorithm/Online.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If the step on `r` halts with output `o`, the run halts there.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Online Online.OnlineAlgorithm in
variable {α σ β : Type*} in
/-- If the step on `r` halts with output `o`, the run halts there. -/
@[simp] theorem Online.OnlineAlgorithm.run_cons_some (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (o : β) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', some o)) :
    alg.run s (r :: rs) = (s', some o) := by
  rw [run_cons, h]
