import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.unionSubtype

Topic: computability   Node: 674433ce6daf

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.unionSubtype`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Union.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The union of two LTSs that have common supertypes for states and labels.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
variable {State : Type u} {Label : Type v} in
/-- The union of two LTSs that have common supertypes for states and labels. -/
def Cslib.LTS.unionSubtype
{S1 : State → Prop} {L1 : Label → Prop} {S2 : State → Prop} {L2 : Label → Prop}
[DecidablePred S1] [DecidablePred L1] [DecidablePred S2] [DecidablePred L2]
(lts1 : LTS (@Subtype State S1) (@Subtype Label L1))
(lts2 : LTS (@Subtype State S2) (@Subtype Label L2)) :
  LTS State Label where
  Tr := fun s μ s' =>
    if h : S1 s ∧ L1 μ ∧ S1 s' then
      lts1.Tr ⟨s, h.1⟩ ⟨μ, h.2.1⟩ ⟨s', h.2.2⟩
    else if h : S2 s ∧ L2 μ ∧ S2 s' then
      lts2.Tr ⟨s, h.1⟩ ⟨μ, h.2.1⟩ ⟨s', h.2.2⟩
    else
      False
