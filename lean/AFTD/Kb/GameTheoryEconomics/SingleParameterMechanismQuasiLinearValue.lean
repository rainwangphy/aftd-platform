import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism

/-!
# SingleParameterMechanism.quasiLinearValue

Topic: mechanism_design   Node: 9686fac57c91

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.quasiLinearValue`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Quasi-linear value in the single-parameter setting: agent `i` with true type `θᵢ` gets allocation `xᵢ`, worth `θᵢ * xᵢ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [DecidableEq I] {R : Type*} in
variable (M : SingleParameterMechanism I R) in
/-- Quasi-linear value in the single-parameter setting: agent `i` with true type `θᵢ` gets allocation `xᵢ`, worth `θᵢ * xᵢ`. -/
def SingleParameterMechanism.quasiLinearValue [Mul R]
    (x θ : I → R) (i : I) : R :=
  θ i * x i
