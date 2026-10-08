import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisLamB0
import AFTD.Kb.GameTheoryEconomics.LoomisMuB0
import AFTD.Kb.GameTheoryEconomics.LoomisLoomisValueIJ2
import AFTD.Kb.GameTheoryEconomics.LoomisLamB0LeMuB0
import AFTD.Kb.GameTheoryEconomics.LoomisXB
import AFTD.Kb.GameTheoryEconomics.LoomisXA
import AFTD.Kb.GameTheoryEconomics.LoomisExistsXxLamB0
import AFTD.Kb.GameTheoryEconomics.LoomisAy
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.GameTheoryEconomics.LoomisExistsYyMuB0
import AFTD.Kb.GameTheoryEconomics.LoomisColOffset
import AFTD.Kb.GameTheoryEconomics.LoomisRowOffset
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.LoomisXByPos
import AFTD.Kb.Optimization.WsumWsumComm
import AFTD.Kb.GameTheoryEconomics.LoomisXBySwap
import AFTD.Kb.GameTheoryEconomics.LoomisWsumConstMul
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAux
import AFTD.Kb.GameTheoryEconomics.LoomisColRatio
import AFTD.Kb.GameTheoryEconomics.LoomisXBPos
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxLeLamB0
import AFTD.Kb.GameTheoryEconomics.LoomisDropCol
import AFTD.Kb.GameTheoryEconomics.LoomisDropColIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisExtendDropColumn
import AFTD.Kb.GameTheoryEconomics.LoomisAyExtendDropColumn
import AFTD.Kb.GameTheoryEconomics.LoomisByExtendDropColumn
import AFTD.Kb.GameTheoryEconomics.LoomisRowRatio
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxGeMuB0
import AFTD.Kb.Optimization.MixGtOfGtNbh
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.GameTheoryEconomics.LoomisColOffsetMix
import AFTD.Kb.Optimization.LinearCombGtOfGeGt
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxGtOfColOffsetPos
import AFTD.Kb.GameTheoryEconomics.LoomisByPos
import AFTD.Kb.GameTheoryEconomics.LoomisDropRow
import AFTD.Kb.GameTheoryEconomics.LoomisDropRowIsPositive
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisExtendDropRow
import AFTD.Kb.GameTheoryEconomics.LoomisXAExtendDropRow
import AFTD.Kb.GameTheoryEconomics.LoomisXBExtendDropRow
import AFTD.Kb.GameTheoryEconomics.LoomisRowOffsetMix
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxLtOfRowOffsetPos
import AFTD.Kb.Optimization.StdSimplexMixApply
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.GameTheoryEconomics.Strict

/-!
# Loomis.loomis_value_eq_aux

Topic: equilibria   Node: 5dcb06a77f09

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.loomis_value_eq_aux`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

**Loomis induction**: `lamB0 A B = muB0 A B` for any finite positive-`B` matrix pair with `2 ≤ |I| + |J|`, by strong induction on the total dimension.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Loomis in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- **Loomis induction**: `lamB0 A B = muB0 A B` for any finite positive-`B` matrix pair with `2 ≤ |I| + |J|`, by strong induction on the total dimension. -/
theorem Loomis.loomis_value_eq_aux :
    ∀ (n : ℕ), 2 ≤ n →
    ∀ {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J],
      n = Fintype.card I + Fintype.card J →
      ∀ (A B : I → J → ℝ), IsPositive B → lamB0 A B = muB0 A B := by
  intro n Hgt
  induction n, Hgt using Nat.le_induction with
  | base =>
      intro I J _ _ _ _ Hn A B hB
      exact loomis_value_IJ_2 Hn hB
  | succ n _ IH =>
      intro I J _ _ _ _ Hn A B hB
      classical
      rcases (lamB0_le_muB0 A B hB).lt_or_eq with hlt | heq
      swap
      · exact heq
      exfalso
      obtain ⟨xx, Hxx⟩ := exists_xx_lamB0 A B hB
      obtain ⟨yy, Hyy⟩ := exists_yy_muB0 A B hB
      -- The Hxx/Hyy say `colOffset ≥ 0` / `rowOffset ≥ 0` everywhere.
      have HxxOff : ∀ j, 0 ≤ colOffset A B (lamB0 A B) xx j := by
        intro j; unfold colOffset; linarith [Hxx j]
      have HyyOff : ∀ i, 0 ≤ rowOffset A B (muB0 A B) yy i := by
        intro i; unfold rowOffset; linarith [Hyy i]
      -- If both are identically zero, we get `lamB0 = muB0`, contradiction.
      have exits_ij :
          (∃ j : J, 0 < colOffset A B (lamB0 A B) xx j)
            ∨ (∃ i : I, 0 < rowOffset A B (muB0 A B) yy i) := by
        by_contra HP
        push_neg at HP
        obtain ⟨HP1, HP2⟩ := HP
        have HxxZero : ∀ j, colOffset A B (lamB0 A B) xx j = 0 :=
          fun j => le_antisymm (HP1 j) (HxxOff j)
        have HyyZero : ∀ i, rowOffset A B (muB0 A B) yy i = 0 :=
          fun i => le_antisymm (HP2 i) (HyyOff i)
        -- These give wsum yy (colOffset xx ·) = 0 and wsum xx (rowOffset yy ·) = 0.
        set xxByy : ℝ := wsum xx (fun i => By B yy i)
        have hxxByy_pos : 0 < xxByy := xBy_pos hB xx yy
        -- wsum yy (xA xx ·) = lamB0 * (wsum yy (xB xx ·)) and
        -- wsum xx (Ay yy ·) = muB0 * (wsum xx (By yy ·)) = muB0 * xxByy
        have h_pair_swap :
            wsum xx (fun i => Ay A yy i) = wsum yy (fun j => xA A xx j) := by
          unfold Ay xA
          exact wsum_wsum_comm xx yy A
        have h_xxByy_swap :
            wsum yy (fun j => xB B xx j) = xxByy := by
          show wsum yy (fun j => xB B xx j) = wsum xx (fun i => By B yy i)
          exact (xBy_swap B xx yy).symm
        -- From HxxZero: wsum yy (xA xx ·) = lamB0 * wsum yy (xB xx ·)
        have h_lhs : wsum yy (fun j => xA A xx j) = lamB0 A B * xxByy := by
          rw [← h_xxByy_swap]
          have : wsum yy (fun j => xA A xx j)
              = wsum yy (fun j => lamB0 A B * xB B xx j) := by
            refine congrArg (wsum yy) (funext ?_)
            intro j
            have := HxxZero j
            unfold colOffset at this
            linarith
          rw [this, wsum_const_mul]
        -- From HyyZero: wsum xx (Ay yy ·) = muB0 * xxByy
        have h_rhs : wsum xx (fun i => Ay A yy i) = muB0 A B * xxByy := by
          have : wsum xx (fun i => Ay A yy i)
              = wsum xx (fun i => muB0 A B * By B yy i) := by
            refine congrArg (wsum xx) (funext ?_)
            intro i
            have := HyyZero i
            unfold rowOffset at this
            linarith
          rw [this, wsum_const_mul]
        have heq2 : lamB0 A B = muB0 A B := by
          have hcombo : lamB0 A B * xxByy = muB0 A B * xxByy := by
            linarith [h_lhs, h_pair_swap, h_rhs]
          exact mul_right_cancel₀ hxxByy_pos.ne' hcombo
        linarith
      rcases exits_ij with ⟨j₀, HJ⟩ | ⟨i₀, HI⟩
      · -------------------- Column-drop case --------------------
        -- |J| ≥ 2 because strict ineq at j₀ ⇒ otherwise lamB.aux xx > lamB0,
        -- contradicting lamB.aux ≤ lamB0.
        have cardJ_ne_one : Fintype.card J ≠ 1 := by
          intro hcardJ
          obtain ⟨j, hj⟩ := Finset.card_eq_one.1 (Finset.card_univ.trans hcardJ)
          have hj0_eq : j₀ = j := by
            have hmem : j₀ ∈ (Finset.univ : Finset J) := Finset.mem_univ _
            rw [hj] at hmem
            exact Finset.mem_singleton.1 hmem
          -- lamB.aux xx evaluated at the unique column j₀
          have hlamB_xx : lamB.aux A B xx = colRatio A B xx j₀ := by
            simp [lamB.aux, hj0_eq, hj]
          have hxxB : 0 < xB B xx j₀ := xB_pos hB xx j₀
          have hratio_gt : lamB0 A B < colRatio A B xx j₀ := by
            unfold colRatio
            rw [lt_div_iff₀ hxxB]
            have hHJ := HJ; unfold colOffset at hHJ; linarith
          have hle : lamB.aux A B xx ≤ lamB0 A B := lamB.aux.le_lamB0 hB xx
          rw [hlamB_xx] at hle
          linarith
        have cardJ_ge_two : 2 ≤ Fintype.card J := by
          have hpos : 1 ≤ Fintype.card J := Fintype.card_pos
          omega
        have nonempty_J' : Nonempty {j : J // j ≠ j₀} := by
          obtain ⟨j, hj⟩ : ∃ j : J, j ≠ j₀ := by
            by_contra H1
            push_neg at H1
            have hsubsing : Fintype.card J ≤ 1 := by
              have hsingle : (Finset.univ : Finset J) = {j₀} := by ext; simp [H1]
              simpa [← Finset.card_univ, hsingle]
            omega
          exact ⟨⟨j, hj⟩⟩
        haveI : Nonempty {j : J // j ≠ j₀} := nonempty_J'
        have cardn : n = Fintype.card I + Fintype.card {j : J // j ≠ j₀} := by
          have hJ' : Fintype.card {j : J // j ≠ j₀} = Fintype.card J - 1 := by
            simp [Fintype.card_subtype_compl]
          have hposJ : 1 ≤ Fintype.card J := Fintype.card_pos
          omega
        -- Apply IH to the column-dropped game.
        let A' : I → {j : J // j ≠ j₀} → ℝ := dropCol A j₀
        let B' : I → {j : J // j ≠ j₀} → ℝ := dropCol B j₀
        have hB' : IsPositive B' := dropCol.IsPositive hB j₀
        have IH' : lamB0 A' B' = muB0 A' B' := IH cardn A' B' hB'
        -- Show muB0 A B ≤ muB0 A' B' via the extend-by-zero trick.
        have h_mu_mono : muB0 A B ≤ muB0 A' B' := by
          apply le_ciInf
          intro y'
          have hwsum_Ay : ∀ i,
              Ay A (MinimaxLoomis.extendDropColumn j₀ y') i = Ay A' y' i :=
            fun i => Ay_extendDropColumn i A j₀ y'
          have hwsum_By : ∀ i,
              By B (MinimaxLoomis.extendDropColumn j₀ y') i = By B' y' i :=
            fun i => By_extendDropColumn i B j₀ y'
          have hmuA' : muB.aux A' B' y'
              = muB.aux A B (MinimaxLoomis.extendDropColumn j₀ y') := by
            simp only [muB.aux]
            congr 1
            ext i
            unfold rowRatio
            rw [hwsum_Ay i, hwsum_By i]
          rw [hmuA']
          exact muB.aux.ge_muB0 hB (MinimaxLoomis.extendDropColumn j₀ y')
        have lamB0_lt_lamB0' : lamB0 A B < lamB0 A' B' := by
          calc lamB0 A B < muB0 A B := hlt
            _ ≤ muB0 A' B' := h_mu_mono
            _ = lamB0 A' B' := IH'.symm
        -- Get the inductive optimiser `xx'` for the restricted game.
        obtain ⟨xx', Hxx'⟩ := exists_xx_lamB0 A' B' hB'
        -- On non-j₀ columns, `colOffset A B lamB0 xx' j > 0`.
        have HxxOff' : ∀ j : J, j ≠ j₀ →
            0 < colOffset A B (lamB0 A B) xx' j := by
          intro j hj
          have hxx'_j : lamB0 A' B' * xB B' xx' ⟨j, hj⟩
              ≤ xA A' xx' ⟨j, hj⟩ := Hxx' ⟨j, hj⟩
          have : lamB0 A B * xB B xx' j < xA A xx' j := by
            have hxB'_xB : xB B' xx' ⟨j, hj⟩ = xB B xx' j := rfl
            have hxA'_xA : xA A' xx' ⟨j, hj⟩ = xA A xx' j := rfl
            have hxBpos : 0 < xB B xx' j := xB_pos hB xx' j
            calc lamB0 A B * xB B xx' j
                < lamB0 A' B' * xB B xx' j := by
                  exact (mul_lt_mul_iff_of_pos_right hxBpos).mpr lamB0_lt_lamB0'
              _ ≤ xA A xx' j := by
                  rw [← hxB'_xB, ← hxA'_xA]; exact hxx'_j
          unfold colOffset; linarith
        -- For j = j₀ use the neighborhood-of-1 continuity lemma; for j ≠ j₀
        -- the convex combination keeps strict positivity.
        obtain ⟨t, ht0pos, ht1lt, hstrict_j0_raw⟩ :
            ∃ t : ℝ, 0 < t ∧ t < 1 ∧
              0 < t * colOffset A B (lamB0 A B) xx j₀
                + (1 - t) * colOffset A B (lamB0 A B) xx' j₀ :=
          mix_gt_of_gt_nbh _ _ _ HJ
        have ht₀ : 0 ≤ t := le_of_lt ht0pos
        have ht₁ : t ≤ 1 := le_of_lt ht1lt
        have hstrict_j0 :
            0 < colOffset A B (lamB0 A B)
                  (stdSimplex.mix t ht₀ ht₁ xx xx') j₀ := by
          rw [colOffset_mix]; exact hstrict_j0_raw
        -- Assemble strict on every j.
        have hAll : ∀ j,
            0 < colOffset A B (lamB0 A B)
                  (stdSimplex.mix t ht₀ ht₁ xx xx') j := by
          intro j
          by_cases hj : j = j₀
          · rw [hj]; exact hstrict_j0
          · rw [colOffset_mix]
            exact linear_comb_gt_of_ge_gt
              (colOffset A B (lamB0 A B) xx j)
              (colOffset A B (lamB0 A B) xx' j) 0
              (HxxOff j) (HxxOff' j hj) ht₀ ht1lt
        -- Hence lamB.aux at the combination strictly exceeds lamB0, contradiction.
        have hgt : lamB0 A B
            < lamB.aux A B (stdSimplex.mix t ht₀ ht₁ xx xx') :=
          lamB.aux_gt_of_colOffset_pos hB hAll
        have hle : lamB.aux A B (stdSimplex.mix t ht₀ ht₁ xx xx') ≤ lamB0 A B :=
          lamB.aux.le_lamB0 hB _
        linarith
      · -------------------- Row-drop case --------------------
        have cardI_ne_one : Fintype.card I ≠ 1 := by
          intro hcardI
          obtain ⟨i, hi⟩ := Finset.card_eq_one.1 (Finset.card_univ.trans hcardI)
          have hi0_eq : i₀ = i := by
            have hmem : i₀ ∈ (Finset.univ : Finset I) := Finset.mem_univ _
            rw [hi] at hmem
            exact Finset.mem_singleton.1 hmem
          have hmuB_yy : muB.aux A B yy = rowRatio A B yy i₀ := by
            simp [muB.aux, hi0_eq, hi]
          have hyyB : 0 < By B yy i₀ := By_pos hB yy i₀
          have hratio_lt : rowRatio A B yy i₀ < muB0 A B := by
            unfold rowRatio
            rw [div_lt_iff₀ hyyB]
            have hHI := HI; unfold rowOffset at hHI; linarith
          have hge : muB0 A B ≤ muB.aux A B yy := muB.aux.ge_muB0 hB yy
          rw [hmuB_yy] at hge
          linarith
        have cardI_ge_two : 2 ≤ Fintype.card I := by
          have hpos : 1 ≤ Fintype.card I := Fintype.card_pos
          omega
        have nonempty_I' : Nonempty {i : I // i ≠ i₀} := by
          obtain ⟨i, hi⟩ : ∃ i : I, i ≠ i₀ := by
            by_contra H1
            push_neg at H1
            have hsubsing : Fintype.card I ≤ 1 := by
              have hsingle : (Finset.univ : Finset I) = {i₀} := by ext; simp [H1]
              simpa [← Finset.card_univ, hsingle]
            omega
          exact ⟨⟨i, hi⟩⟩
        haveI : Nonempty {i : I // i ≠ i₀} := nonempty_I'
        have cardn : n = Fintype.card {i : I // i ≠ i₀} + Fintype.card J := by
          have hI' : Fintype.card {i : I // i ≠ i₀} = Fintype.card I - 1 := by
            simp [Fintype.card_subtype_compl]
          have hposI : 1 ≤ Fintype.card I := Fintype.card_pos
          omega
        let A' : {i : I // i ≠ i₀} → J → ℝ := dropRow A i₀
        let B' : {i : I // i ≠ i₀} → J → ℝ := dropRow B i₀
        have hB' : IsPositive B' := dropRow.IsPositive hB i₀
        have IH' : lamB0 A' B' = muB0 A' B' := IH cardn A' B' hB'
        have h_lam_mono : lamB0 A' B' ≤ lamB0 A B := by
          apply ciSup_le
          intro x'
          have hwsum_xA : ∀ j,
              xA A (MinimaxLoomis.extendDropRow i₀ x') j = xA A' x' j :=
            fun j => xA_extendDropRow j A i₀ x'
          have hwsum_xB : ∀ j,
              xB B (MinimaxLoomis.extendDropRow i₀ x') j = xB B' x' j :=
            fun j => xB_extendDropRow j B i₀ x'
          have hlamA' : lamB.aux A' B' x'
              = lamB.aux A B (MinimaxLoomis.extendDropRow i₀ x') := by
            simp only [lamB.aux]
            congr 1
            ext j
            unfold colRatio
            rw [hwsum_xA j, hwsum_xB j]
          rw [hlamA']
          exact lamB.aux.le_lamB0 hB (MinimaxLoomis.extendDropRow i₀ x')
        have muB0_gt_muB0' : muB0 A' B' < muB0 A B := by
          calc muB0 A' B' = lamB0 A' B' := IH'.symm
            _ ≤ lamB0 A B := h_lam_mono
            _ < muB0 A B := hlt
        obtain ⟨yy', Hyy'⟩ := exists_yy_muB0 A' B' hB'
        have HyyOff' : ∀ i : I, i ≠ i₀ →
            0 < rowOffset A B (muB0 A B) yy' i := by
          intro i hi
          have hyy'_i : Ay A' yy' ⟨i, hi⟩
              ≤ muB0 A' B' * By B' yy' ⟨i, hi⟩ := Hyy' ⟨i, hi⟩
          have : Ay A yy' i < muB0 A B * By B yy' i := by
            have hAy'_Ay : Ay A' yy' ⟨i, hi⟩ = Ay A yy' i := rfl
            have hBy'_By : By B' yy' ⟨i, hi⟩ = By B yy' i := rfl
            have hBypos : 0 < By B yy' i := By_pos hB yy' i
            calc Ay A yy' i
                = Ay A' yy' ⟨i, hi⟩ := hAy'_Ay.symm
              _ ≤ muB0 A' B' * By B' yy' ⟨i, hi⟩ := hyy'_i
              _ = muB0 A' B' * By B yy' i := by rw [hBy'_By]
              _ < muB0 A B * By B yy' i :=
                  (mul_lt_mul_iff_of_pos_right hBypos).mpr muB0_gt_muB0'
          unfold rowOffset; linarith
        obtain ⟨t, ht0pos, ht1lt, hstrict_i0_raw⟩ :
            ∃ t : ℝ, 0 < t ∧ t < 1 ∧
              0 < t * rowOffset A B (muB0 A B) yy i₀
                + (1 - t) * rowOffset A B (muB0 A B) yy' i₀ :=
          mix_gt_of_gt_nbh _ _ _ HI
        have ht₀ : 0 ≤ t := le_of_lt ht0pos
        have ht₁ : t ≤ 1 := le_of_lt ht1lt
        have hstrict_i0 :
            0 < rowOffset A B (muB0 A B)
                  (stdSimplex.mix t ht₀ ht₁ yy yy') i₀ := by
          rw [rowOffset_mix]; exact hstrict_i0_raw
        have hAll : ∀ i,
            0 < rowOffset A B (muB0 A B)
                  (stdSimplex.mix t ht₀ ht₁ yy yy') i := by
          intro i
          by_cases hi : i = i₀
          · rw [hi]; exact hstrict_i0
          · rw [rowOffset_mix]
            exact linear_comb_gt_of_ge_gt
              (rowOffset A B (muB0 A B) yy i)
              (rowOffset A B (muB0 A B) yy' i) 0
              (HyyOff i) (HyyOff' i hi) ht₀ ht1lt
        have hlt' : muB.aux A B (stdSimplex.mix t ht₀ ht₁ yy yy') < muB0 A B :=
          muB.aux_lt_of_rowOffset_pos hB hAll
        have hge : muB0 A B ≤ muB.aux A B (stdSimplex.mix t ht₀ ht₁ yy yy') :=
          muB.aux.ge_muB0 hB _
        linarith
