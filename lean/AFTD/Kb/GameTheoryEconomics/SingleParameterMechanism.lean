import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers

/-!
# SingleParameterMechanism

Topic: mechanism_design   Node: 048320f0ebac

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A single-parameter mechanism. Each agent `i` has a single private type `θ_i : R` (their "value per unit"). The allocation gives each agent a scalar `x_i : R` (typically in `[0, 1]`, interpreted as probability of winning or fractional quantity received). Payments are of the same scalar type `R`; utility is quasi-linear: `θ_i · x_i - p_i`. In practice `R = ℝ`. The structure is kept polymorphic for generality. This is the canonical setting for Myerson's revenue-optimal auction theorem and for characterizing implementable (DSIC) allocation rules via monotonicity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A single-parameter mechanism. Each agent `i` has a single private type `θ_i : R` (their "value per unit"). The allocation gives each agent a scalar `x_i : R` (typically in `[0, 1]`, interpreted as probability of winning or fractional quantity received). Payments are of the same scalar type `R`; utility is quasi-linear: `θ_i · x_i - p_i`. In practice `R = ℝ`. The structure is kept polymorphic for generality. This is the canonical setting for Myerson's revenue-optimal auction theorem and for characterizing implementable (DSIC) allocation rules via monotonicity. -/
structure SingleParameterMechanism (I : Type*) (R : Type*)
    extends MechanismWithTransfers I (fun _ => R) (I → R) R
