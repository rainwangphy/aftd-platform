import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMTransitivity
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.VNMNotTransitivePref
import AFTD.Kb.GameTheoryEconomics.VNMNotContinuousPref

/-!
# VNM.NotTransitive.not_transitive

Topic: general_equilibrium   Node: 1cee917979bf

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotTransitive.not_transitive`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotTransitive.not_transitive
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotTransitive.not_transitive : ¬ Transitivity pref := by
  intro h
  -- Construct three lotteries witnessing intransitivity:
  -- L₁ = (0.4, 0.1, 0.5), L₂ = (0.3, 0.3, 0.4), L₃ = (0.5, 0.2, 0.3)
  -- pref L₁ L₂ via component 0: 0.4 ≥ 0.3
  -- pref L₂ L₃ via component 1: 0.3 ≥ 0.2
  -- ¬pref L₁ L₃: 0.4 < 0.5 and 0.1 < 0.2
  let L₁ : Lottery ℚ (Fin 3) := ⟨![2/5, 1/10, 1/2], by
    refine ⟨fun i => by fin_cases i <;> simp (config := { decide := true }) [*] <;> (try norm_num), ?_⟩
    simp [Fin.sum_univ_three]; ring⟩
  let L₂ : Lottery ℚ (Fin 3) := ⟨![3/10, 3/10, 2/5], by
    refine ⟨fun i => by fin_cases i <;> simp (config := { decide := true }) [*] <;> (try norm_num), ?_⟩
    simp [Fin.sum_univ_three]; ring⟩
  let L₃ : Lottery ℚ (Fin 3) := ⟨![1/2, 1/5, 3/10], by
    refine ⟨fun i => by fin_cases i <;> simp (config := { decide := true }) [*] <;> (try norm_num), ?_⟩
    simp [Fin.sum_univ_three]; ring⟩
  have h12 : pref L₁ L₂ := by left; show (2 : ℚ)/5 ≥ 3/10; norm_num
  have h23 : pref L₂ L₃ := by right; show (3 : ℚ)/10 ≥ 1/5; norm_num
  have h13 := h L₁ L₂ L₃ h12 h23
  rcases h13 with h0 | h1
  · exact absurd h0 (by show ¬((2 : ℚ)/5 ≥ 1/2); norm_num)
  · exact absurd h1 (by show ¬((1 : ℚ)/10 ≥ 1/5); norm_num)
