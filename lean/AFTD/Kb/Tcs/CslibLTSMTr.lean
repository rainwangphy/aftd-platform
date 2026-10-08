import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.MTr

Topic: computability   Node: 0da954b404e4

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MTr`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Definition of a multistep transition. (Implementation note: compared to [Montesi2023], we choose stepL instead of stepR as fundamental rule. This makes working with lists of labels more convenient, because we follow the same construction. It is also similar to what is done in the `SimpleGraph` library in mathlib.)
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- Definition of a multistep transition. (Implementation note: compared to [Montesi2023], we choose stepL instead of stepR as fundamental rule. This makes working with lists of labels more convenient, because we follow the same construction. It is also similar to what is done in the `SimpleGraph` library in mathlib.) -/
@[grind, mk_iff]
inductive Cslib.LTS.MTr (lts : LTS State Label) : State → List Label → State → Prop where
  | refl {s : State} : lts.MTr s [] s
  | stepL {s1 : State} {μ : Label} {s2 : State} {μs : List Label} {s3 : State} :
    lts.Tr s1 μ s2 → lts.MTr s2 μs s3 →
    lts.MTr s1 (μ :: μs) s3
