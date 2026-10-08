import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy

/-!
# OnlineLearning.arbitraryMixedStrategy

Topic: equilibria   Node: 68b12164a5ec

Provenance: formalization of a published result. Source: TCSlib, `OnlineLearning.arbitraryMixedStrategy`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A concrete mixed strategy used only to prove that the type of mixed strategies is nonempty. It puts all mass on one arbitrary action.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- A concrete mixed strategy used only to prove that the type of mixed strategies is nonempty. It puts all mass on one arbitrary action. -/
noncomputable def OnlineLearning.arbitraryMixedStrategy (n : ℕ) [NeZero n] : MixedStrategy n where
  weights i := if i = Classical.choice inferInstance then 1 else 0
  nonneg i := by
    split <;> positivity
  sum_one := by
    classical
    let i₀ : Fin n := Classical.choice inferInstance
    change ∑ i : Fin n, (if i = i₀ then (1 : ℝ) else 0) = 1
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
