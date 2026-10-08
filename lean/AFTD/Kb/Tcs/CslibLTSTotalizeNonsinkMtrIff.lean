import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSTotalize
import AFTD.Kb.Tcs.CslibLTSTotalizeNoSinkToNonsink
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff
import AFTD.Kb.Tcs.CslibLTSTotalizeNonsinkTrIff
import AFTD.Kb.Tcs.CslibLTSInstTotalOptionTotalize

/-!
# Cslib.LTS.totalize.nonsink_mtr_iff

Topic: computability   Node: 5af91d8cbd87

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.totalize.nonsink_mtr_iff`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Total.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In `totalize`, the multistep transitions between non-sink states correspond exactly to the multistep transitions in the original LTS.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
/-- In `totalize`, the multistep transitions between non-sink states correspond exactly to the multistep transitions in the original LTS. -/
@[simp]
theorem Cslib.LTS.totalize.nonsink_mtr_iff {μs : List Label} {s t : State} :
    lts.totalize.MTr (some s) μs (some t) ↔ lts.MTr s μs t := by
  constructor <;> intro h
  · generalize h_s : (some s : Option State) = s'
    generalize h_t : (some t : Option State) = t'
    rw [h_s, h_t] at h
    induction h generalizing s
    case refl _ => grind [MTr]
    case stepL t1' μ t2' μs t3' h_tr h_mtr h_ind =>
      obtain ⟨rfl⟩ := h_s
      cases t2'
      case some t2 => grind [MTr, totalize.nonsink_tr_iff.mp h_tr]
      case none => grind [totalize.no_sink_to_nonsink]
  · induction h
    case refl _ => grind [MTr]
    case stepL t1 μ t2 μs t3 h_tr h_mtr h_ind =>
      grind [MTr, totalize.nonsink_tr_iff.mpr h_tr]
