import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningArbitraryMixedStrategy
import AFTD.Kb.GameTheoryEconomics.MixedStrategy

/-!
# OnlineLearning.mixedStrategyNonempty

Topic: equilibria   Node: 4f3c4ee3a738

Provenance: formalization of a published result. Source: TCSlib, `OnlineLearning.mixedStrategyNonempty`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The mixed-strategy space is nonempty whenever the underlying action set is nonempty.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The mixed-strategy space is nonempty whenever the underlying action set is nonempty. -/
noncomputable instance OnlineLearning.mixedStrategyNonempty (n : ℕ) [NeZero n] :
    Nonempty (MixedStrategy n) :=
  ⟨arbitraryMixedStrategy n⟩
