import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAux
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumConst
import AFTD.Kb.Optimization.WsumLeWsum
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxBddBelow

/-!
# MinimaxLoomis.mu.aux.bddBelow

Topic: equilibria   Node: 3d3641e974c5

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.mu.aux.bddBelow`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`mu.aux A` is uniformly bounded below on the simplex.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- `mu.aux A` is uniformly bounded below on the simplex. -/
theorem MinimaxLoomis.mu.aux.bddBelow (A : I → J → ℝ) :
    ∃ C, ∀ y, C ≤ mu.aux A y := by
  classical
  let C0 : ℝ :=
    Finset.inf' Finset.univ Finset.univ_nonempty
      (fun j => Finset.inf' Finset.univ Finset.univ_nonempty (fun i => A i j))
  have hAij : ∀ i j, C0 ≤ A i j := by
    intro i j
    calc C0
        ≤ Finset.inf' Finset.univ Finset.univ_nonempty (fun i => A i j) :=
          Finset.inf'_le _ (Finset.mem_univ _)
      _ ≤ A i j := Finset.inf'_le _ (Finset.mem_univ _)
  refine ⟨C0, fun y => ?_⟩
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hrow : C0 ≤ wsum y (fun j => A i₀ j) := by
    calc C0 = wsum y (fun _ => C0) := (wsum_const y C0).symm
      _ ≤ wsum y (fun j => A i₀ j) := wsum_le_wsum y (fun j => hAij i₀ j)
  exact hrow.trans (Finset.le_sup' (fun i => wsum y (fun j => A i j))
    (Finset.mem_univ i₀))
