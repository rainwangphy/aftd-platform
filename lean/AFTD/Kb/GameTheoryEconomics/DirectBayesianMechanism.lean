import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanism

/-!
# DirectBayesianMechanism

Topic: mechanism_design   Node: c8ce3ac52784

Provenance: formalization of a published result. Source: EconCSLib, `DirectBayesianMechanism`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A direct-revelation Bayesian mechanism: agents report in their own type spaces.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A direct-revelation Bayesian mechanism: agents report in their own type spaces. -/
abbrev DirectBayesianMechanism
    (I : Type*) (T : I → Type*) [∀ i, MeasurableSpace (T i)] (O : Type*) :=
  BayesianMechanism I T T O
