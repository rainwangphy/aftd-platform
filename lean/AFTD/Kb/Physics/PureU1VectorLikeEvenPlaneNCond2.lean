import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# PureU1.VectorLikeEvenPlane.n_cond₂

Topic: quantum_field_theory   Node: 63ab136047cb

Provenance: formalization of a published result. Source: Physlib, `PureU1.VectorLikeEvenPlane.n_cond₂`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/QED/AnomalyCancellation/Even/BasisLinear.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PureU1.VectorLikeEvenPlane.n_cond₂
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat Module Finset BigOperators in
variable {n : ℕ} in
lemma PureU1.VectorLikeEvenPlane.n_cond₂ (n : ℕ) : 1 + ((n + n) + 1) = 2 * n.succ := by
  linarith
