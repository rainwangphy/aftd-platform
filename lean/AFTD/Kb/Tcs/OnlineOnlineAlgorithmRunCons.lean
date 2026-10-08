import AFTD.Prelude
import AFTD.Kb.Tcs.OnlineOnlineAlgorithm
import AFTD.Kb.Tcs.OnlineOnlineAlgorithmRun
import AFTD.Kb.Tcs.OnlineOnlineAlgorithmRunNil

/-!
# Online.OnlineAlgorithm.run_cons

Topic: online_algorithms   Node: a70a7e6437c7

Provenance: formalization of a published result. Source: EconCSLib, `Online.OnlineAlgorithm.run_cons`. Lean proof by Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Algorithm/Online.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Online.OnlineAlgorithm.run_cons
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Online Online.OnlineAlgorithm in
variable {α σ β : Type*} in
theorem Online.OnlineAlgorithm.run_cons (alg : OnlineAlgorithm α σ β)
    (s : σ) (r : α) (rs : List α) :
    alg.run s (r :: rs) =
      match alg.step s (some r) with
      | (s', some o) => (s', some o)
      | (s', none)   => alg.run s' rs := rfl
