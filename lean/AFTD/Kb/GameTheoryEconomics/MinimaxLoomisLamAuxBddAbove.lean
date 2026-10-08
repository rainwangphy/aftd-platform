import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAux
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumLeWsum
import AFTD.Kb.Optimization.WsumConst
import AFTD.Kb.Optimization.WsumPureApply

/-!
# MinimaxLoomis.lam.aux.bddAbove

Topic: equilibria   Node: 58e3331c44d4

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.lam.aux.bddAbove`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`lam.aux A` is uniformly bounded above on the simplex.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- `lam.aux A` is uniformly bounded above on the simplex. -/
theorem MinimaxLoomis.lam.aux.bddAbove (A : I → J → ℝ) :
    ∃ C, ∀ x, lam.aux A x ≤ C := by
  classical
  let C0 : ℝ :=
    Finset.sup' Finset.univ Finset.univ_nonempty
      (fun i => Finset.sup' Finset.univ Finset.univ_nonempty (A i))
  have hAij : ∀ i j, A i j ≤ C0 := by
    intro i j
    calc A i j
        ≤ Finset.sup' Finset.univ Finset.univ_nonempty (A i) :=
          Finset.le_sup' _ (Finset.mem_univ _)
      _ ≤ C0 :=
          Finset.le_sup'
            (fun i => Finset.sup' Finset.univ Finset.univ_nonempty (A i))
            (Finset.mem_univ _)
  refine ⟨C0, fun x => ?_⟩
  obtain ⟨j₀⟩ := ‹Nonempty J›
  have hcol : wsum x (fun i => A i j₀) ≤ C0 := by
    calc wsum x (fun i => A i j₀)
        ≤ wsum x (fun _ => C0) := wsum_le_wsum x (fun i => hAij i j₀)
      _ = C0 := wsum_const x C0
  exact (Finset.inf'_le (fun j => wsum x (fun i => A i j))
    (Finset.mem_univ j₀)).trans hcol
