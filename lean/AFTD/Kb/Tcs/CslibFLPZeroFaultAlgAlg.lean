import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFLPAlgorithm
import AFTD.Kb.Tcs.CslibFLPZeroFaultAlgM
import AFTD.Kb.Tcs.CslibFLPZeroFaultAlgS
import AFTD.Kb.Tcs.CslibFLPMessage
import AFTD.Kb.Tcs.CslibFLPProcState

/-!
# Cslib.FLP.ZeroFaultAlg.alg

Topic: distributed   Node: fa9331b0b4ff

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLP.ZeroFaultAlg.alg`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Distributed/FLP/ZeroConsensus.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`alg` is the asynchronous distributed consensus algorithm described above.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Sum Option Multiset in
variable {n : ℕ} (npos : 0 < n) in
/-- `alg` is the asynchronous distributed consensus algorithm described above. -/
def Cslib.FLP.ZeroFaultAlg.alg : Algorithm (Fin n) M S where
  init _ := ()
  next _ _ := ()
  send m _ := match m.msg with
    | inl b =>
      if m.dest = ⟨0, npos⟩ then Multiset.map (fun p ↦ ⟨p, inr b⟩) Finset.univ.val else 0
    | inr _ => 0
  out m _ := match m.msg with
    | inl _ => none
    | inr b => some b
