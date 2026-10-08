import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.GameTheoryEconomics.LoomisAy
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.LoomisColRatio
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAux
import AFTD.Kb.GameTheoryEconomics.LoomisMuB0
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.LoomisXB
import AFTD.Kb.GameTheoryEconomics.LoomisXA
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisSingletonOfCardOne
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisRowRatio
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAux
import AFTD.Kb.GameTheoryEconomics.LoomisLamB0

/-!
# Loomis.loomis_value_IJ_2

Topic: equilibria   Node: ac4e2c031268

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.loomis_value_IJ_2`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Base case of the Loomis induction: a 1×1 matrix pair has the single ratio `A i₀ j₀ / B i₀ j₀` as the common Loomis value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Base case of the Loomis induction: a 1×1 matrix pair has the single ratio `A i₀ j₀ / B i₀ j₀` as the common Loomis value. -/
theorem Loomis.loomis_value_IJ_2 (Hn : 2 = Fintype.card I + Fintype.card J)
    {A B : I → J → ℝ} (_hB : IsPositive B) :
    lamB0 A B = muB0 A B := by
  classical
  have ⟨HSI, HSJ⟩ : Fintype.card I = 1 ∧ Fintype.card J = 1 := by
    have p1 := @Fintype.card_pos I _ _
    have p2 := @Fintype.card_pos J _ _
    refine ⟨?_, ?_⟩ <;> omega
  obtain ⟨i0, hi⟩ := MinimaxLoomis.singleton_of_card_one HSI
  obtain ⟨j0, hj⟩ := MinimaxLoomis.singleton_of_card_one HSJ
  -- On a singleton simplex every distribution puts mass 1 at the single point.
  have Hxx0 : ∀ x : stdSimplex ℝ I, x.val i0 = 1 := by
    intro x
    have hsum : (∑ i : I, x.val i) = 1 := x.property.2
    have hcol : (∑ i : I, x.val i) = x.val i0 := by
      rw [show (Finset.univ : Finset I) = {i0} from hi, Finset.sum_singleton]
    linarith
  have Hyy0 : ∀ y : stdSimplex ℝ J, y.val j0 = 1 := by
    intro y
    have hsum : (∑ j : J, y.val j) = 1 := y.property.2
    have hrow : (∑ j : J, y.val j) = y.val j0 := by
      rw [show (Finset.univ : Finset J) = {j0} from hj, Finset.sum_singleton]
    linarith
  -- Both ratios reduce to A i0 j0 / B i0 j0 regardless of the strategy.
  have HlamB : ∀ x, lamB.aux A B x = A i0 j0 / B i0 j0 := by
    intro x
    simp only [lamB.aux, hj, Finset.inf'_singleton]
    show colRatio A B x j0 = A i0 j0 / B i0 j0
    unfold colRatio xA xB
    have hxA : wsum x (fun i => A i j0) = A i0 j0 := by
      change (∑ i, x.val i * A i j0) = A i0 j0
      rw [show (Finset.univ : Finset I) = {i0} from hi, Finset.sum_singleton,
          Hxx0 x, one_mul]
    have hxB : wsum x (fun i => B i j0) = B i0 j0 := by
      change (∑ i, x.val i * B i j0) = B i0 j0
      rw [show (Finset.univ : Finset I) = {i0} from hi, Finset.sum_singleton,
          Hxx0 x, one_mul]
    rw [hxA, hxB]
  have HmuB : ∀ y, muB.aux A B y = A i0 j0 / B i0 j0 := by
    intro y
    simp only [muB.aux, hi, Finset.sup'_singleton]
    show rowRatio A B y i0 = A i0 j0 / B i0 j0
    unfold rowRatio Ay By
    have hAy : wsum y (fun j => A i0 j) = A i0 j0 := by
      change (∑ j, y.val j * A i0 j) = A i0 j0
      rw [show (Finset.univ : Finset J) = {j0} from hj, Finset.sum_singleton,
          Hyy0 y, one_mul]
    have hBy : wsum y (fun j => B i0 j) = B i0 j0 := by
      change (∑ j, y.val j * B i0 j) = B i0 j0
      rw [show (Finset.univ : Finset J) = {j0} from hj, Finset.sum_singleton,
          Hyy0 y, one_mul]
    rw [hAy, hBy]
  rw [lamB0, iSup_congr HlamB, ciSup_const, muB0, iInf_congr HmuB, ciInf_const]
