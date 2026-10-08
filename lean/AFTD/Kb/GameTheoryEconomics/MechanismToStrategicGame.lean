import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Mechanism
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# Mechanism.toStrategicGame

Topic: mechanism_design   Node: f73a5d0ffab8

Provenance: formalization of a published result. Source: EconCSLib, `Mechanism.toStrategicGame`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBasic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The strategic game induced by a mechanism and a utility function. Each agent's strategy space is their type space `T i` (they choose what to report). Agent `i`'s payoff from report profile `r` under true type `tᵢ` is `utility (M.outcome r) tᵢ i`. The utility function `u : O → (∀ i, T i) → I → U` takes: - the outcome chosen by the mechanism - the true type profile (for computing each agent's value) - the agent index This captures the standard setup: agents have private types, the mechanism chooses an outcome based on reports, and each agent evaluates the outcome according to their true type.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [DecidableEq I] {T : I → Type*} {O U : Type*} in
variable (M : Mechanism I T O) (u : O → (∀ i, T i) → I → U) in
/-- The strategic game induced by a mechanism and a utility function. Each agent's strategy space is their type space `T i` (they choose what to report). Agent `i`'s payoff from report profile `r` under true type `tᵢ` is `utility (M.outcome r) tᵢ i`. The utility function `u : O → (∀ i, T i) → I → U` takes: - the outcome chosen by the mechanism - the true type profile (for computing each agent's value) - the agent index This captures the standard setup: agents have private types, the mechanism chooses an outcome based on reports, and each agent evaluates the outcome according to their true type. -/
def Mechanism.toStrategicGame (v : ∀ i, T i) : EconCSLib.StrategicGame I U where
  strategy := T
  payoff r i := u (M.outcome r) v i
