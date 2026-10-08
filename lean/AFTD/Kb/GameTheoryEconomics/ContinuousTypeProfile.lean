import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TypeCDF

/-!
# ContinuousTypeProfile

Topic: mechanism_design   Node: 0d71c887a313

Provenance: formalization of a published result. Source: EconCSLib, `ContinuousTypeProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Agent-specific continuous private-value data.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
/-- Agent-specific continuous private-value data. -/
structure ContinuousTypeProfile (I : Type*) where
  /-- Agent-specific upper bounds `ωᵢ` for the type support. -/
  omega : I → ℝ
  /-- Agent-specific CDFs `Fᵢ` on `[0, ωᵢ]`. -/
  cdf : ∀ i, TypeCDF (omega i)
