import AFTD.Prelude

/-!
# BayesianMechanism.Strategy

Topic: mechanism_design   Node: e316baf97990

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanism.Strategy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A pure reporting strategy in an incomplete-information mechanism: an agent maps each possible true type to a report/message.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {O : Type*} in
/-- A pure reporting strategy in an incomplete-information mechanism: an agent maps each possible true type to a report/message. -/
abbrev BayesianMechanism.Strategy (Tᵢ : Type*) (Mᵢ : Type*) := Tᵢ → Mᵢ
