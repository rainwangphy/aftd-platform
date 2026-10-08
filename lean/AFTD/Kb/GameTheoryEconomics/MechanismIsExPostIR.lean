import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Mechanism

/-!
# Mechanism.IsExPostIR

Topic: mechanism_design   Node: ef0ab220990b

Provenance: formalization of a published result. Source: EconCSLib, `Mechanism.IsExPostIR`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A mechanism is (Ex-Post) Individually Rational if every agent gets nonneg utility from truthful reporting, regardless of others' reports.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [DecidableEq I] {T : I → Type*} {O U : Type*} in
variable (M : Mechanism I T O) (u : O → (∀ i, T i) → I → U) in
/-- A mechanism is (Ex-Post) Individually Rational if every agent gets nonneg utility from truthful reporting, regardless of others' reports. -/
def Mechanism.IsExPostIR [Preorder U] [Zero U] : Prop :=
  ∀ v : (∀ i, T i), ∀ i : I, ∀ r : (∀ i, T i),
    0 ≤ u (M.outcome (Function.update r i (v i))) v i
