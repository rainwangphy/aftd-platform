import AFTD.Prelude
import AFTD.Kb.Tcs.OnlineOnlineAlgorithm

/-!
# Online.OnlineAlgorithm.run

Topic: online_algorithms   Node: 03901ff49372

Provenance: formalization of a published result. Source: EconCSLib, `Online.OnlineAlgorithm.run`. Lean proof by Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Algorithm/Online.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Drive the machine across the requests, halting at the **first** step that emits an output. When the genuine requests are exhausted without a commitment, the machine is given the **end-of-input** step `step _ none` — its last chance to decide, since it never knew which request was last — and its `(state, output)` pair *is* the result. So `(run s rs).1` is the terminal state and `(run s rs).2` is the decision.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α σ β : Type*} in
/-- Drive the machine across the requests, halting at the **first** step that emits an output. When the genuine requests are exhausted without a commitment, the machine is given the **end-of-input** step `step _ none` — its last chance to decide, since it never knew which request was last — and its `(state, output)` pair *is* the result. So `(run s rs).1` is the terminal state and `(run s rs).2` is the decision. -/
def Online.OnlineAlgorithm.run (alg : OnlineAlgorithm α σ β) : σ → List α → σ × Option β
  | s, []      => alg.step s none
  | s, r :: rs =>
      match alg.step s (some r) with
      | (s', some o) => (s', some o)
      | (s', none)   => alg.run s' rs
