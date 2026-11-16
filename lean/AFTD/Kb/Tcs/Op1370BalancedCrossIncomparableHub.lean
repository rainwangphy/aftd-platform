import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370LowerIndependentFibers
import AFTD.Kb.Tcs.Op1370IndependentUpperDifferenceHub
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op1370_balanced_cross_incomparable_hub

Topic: combinatorics   Node: 1ed9114f42cd

Provenance: helper lemma. Equality-structure route for the balanced case of OP-1370, arXiv:2611.12199, Conjecture 4.3.

If two mutually incomparable set families each have one quarter of the Boolean cube, the second family has a member Z such that every other member has a common superset with Z inside that family.
-/

open Finset
set_option maxHeartbeats 3000000

lemma op1370_balance_region_arithmetic (m e b c d : ℤ)
    (hm : 0 < m) (he : 0 ≤ e) (hb : m ≤ b) (hc : m ≤ c) (hd : 0 ≤ d)
    (hsum : e + b + c + d = 4 * m)
    (hcorr : (e + b) * (e + c) ≤ 4 * m * e) :
    e = m ∧ b = m ∧ c = m ∧ d = m := by
  have hprod : b * c ≤ e * d := by nlinarith [hcorr]
  have hbc : m * m ≤ b * c := by
    have h : 0 ≤ (b - m) * (c - m) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hsumed : e + d ≤ 2 * m := by linarith
  have hupper : 0 ≤ (2 * m - (e + d)) * (2 * m + (e + d)) :=
    mul_nonneg (by linarith) (by linarith)
  have hed : e * d ≤ m * m := by nlinarith [sq_nonneg (e - d)]
  have hbc_eq : b * c = m * m := le_antisymm (le_trans hprod hed) hbc
  have hbm0 : 0 ≤ m * (b - m) := mul_nonneg (le_of_lt hm) (by linarith)
  have hcm0 : 0 ≤ m * (c - m) := mul_nonneg (le_of_lt hm) (by linarith)
  have hcross : 0 ≤ (b - m) * (c - m) := mul_nonneg (by linarith) (by linarith)
  have hbm : b = m := by nlinarith
  have hcm : c = m := by nlinarith
  have hem : e = m := by nlinarith [sq_nonneg (e - d)]
  have hdm : d = m := by linarith
  exact ⟨hem, hbm, hcm, hdm⟩

theorem op1370_balanced_cross_incomparable_hub (n : ℕ) (hn : 2 ≤ n)
    (F G : Finset (Finset (Fin n)))
    (hinc : ∀ A ∈ F, ∀ B ∈ G, ¬ A ⊆ B ∧ ¬ B ⊆ A)
    (hF : F.card = 2 ^ (n - 2)) (hG : G.card = 2 ^ (n - 2)) :
    ∃ Z ∈ G, ∀ X ∈ G, ∃ W ∈ G, X ⊆ W ∧ Z ⊆ W := by
  classical
  let m : ℕ := 2 ^ (n - 2)
  let U : Finset (Finset (Fin n)) := univ.filter fun X => ∃ A ∈ F, A ⊆ X
  let V : Finset (Finset (Fin n)) := univ.filter fun X => ∃ B ∈ G, B ⊆ X
  let E := U ∩ V
  let B := U \ V
  let C := V \ U
  let D := (U ∪ V)ᶜ
  have hU : IsUpperSet (U : Set (Finset (Fin n))) := by
    intro X Y hXY hX
    obtain ⟨A, hA, hAX⟩ := (mem_filter.mp hX).2
    exact mem_filter.mpr ⟨mem_univ Y, ⟨A, hA, hAX.trans hXY⟩⟩
  have hV : IsUpperSet (V : Set (Finset (Fin n))) := by
    intro X Y hXY hX
    obtain ⟨A, hA, hAX⟩ := (mem_filter.mp hX).2
    exact mem_filter.mpr ⟨mem_univ Y, ⟨A, hA, hAX.trans hXY⟩⟩
  have hFsub : F ⊆ B := by
    intro A hA
    apply mem_sdiff.mpr
    constructor
    · exact mem_filter.mpr ⟨mem_univ A, ⟨A, hA, subset_refl A⟩⟩
    · intro hAV
      obtain ⟨T, hT, hTA⟩ := (mem_filter.mp hAV).2
      exact (hinc A hA T hT).2 hTA
  have hGsub : G ⊆ C := by
    intro A hA
    apply mem_sdiff.mpr
    constructor
    · exact mem_filter.mpr ⟨mem_univ A, ⟨A, hA, subset_refl A⟩⟩
    · intro hAU
      obtain ⟨T, hT, hTA⟩ := (mem_filter.mp hAU).2
      exact (hinc T hT A hA).1 hTA
  have hpow : 2 ^ n = 4 * m := by
    have hn' : n - 2 + 2 = n := by omega
    dsimp [m]
    rw [← hn', pow_add]
    norm_num
    ring
  have hu : U.card = E.card + B.card := by
    have h := card_sdiff_add_card_inter U V
    dsimp [E, B]
    omega
  have hv : V.card = E.card + C.card := by
    have h := card_sdiff_add_card_inter V U
    rw [inter_comm V U] at h
    dsimp [E, C]
    omega
  have hsum : E.card + B.card + C.card + D.card = 4 * m := by
    have h1 := card_union_add_card_inter U V
    have h2 := card_add_card_compl (U ∪ V)
    simp only [Fintype.card_finset, Fintype.card_fin] at h2
    dsimp [E, B, C, D] at *
    omega
  have hb : m ≤ B.card := by
    have := card_le_card hFsub
    dsimp [m] at *
    omega
  have hc : m ≤ C.card := by
    have := card_le_card hGsub
    dsimp [m] at *
    omega
  have hcorr : (E.card + B.card) * (E.card + C.card) ≤ 4 * m * E.card := by
    rw [← hu, ← hv, ← hpow]
    simpa [E] using hU.le_card_inter_finset hV
  have hm : (0 : ℤ) < (m : ℤ) := by dsimp [m]; positivity
  have hsumZ : (E.card : ℤ) + B.card + C.card + D.card = 4 * (m : ℤ) := by exact_mod_cast hsum
  have hcorrZ : ((E.card : ℤ) + B.card) * ((E.card : ℤ) + C.card) ≤ 4 * (m : ℤ) * E.card := by exact_mod_cast hcorr
  have hbZ : (m : ℤ) ≤ B.card := by exact_mod_cast hb
  have hcZ : (m : ℤ) ≤ C.card := by exact_mod_cast hc
  obtain ⟨heZ, hbZ', hcZ', hdZ⟩ := op1370_balance_region_arithmetic m E.card B.card C.card D.card hm (by positivity) hbZ hcZ (by positivity) hsumZ hcorrZ
  have he : E.card = m := by exact_mod_cast heZ
  have hb' : B.card = m := by exact_mod_cast hbZ'
  have hc' : C.card = m := by exact_mod_cast hcZ'
  have hd : D.card = m := by exact_mod_cast hdZ
  have hGC : G = C := eq_of_subset_of_card_le hGsub (by dsimp [m] at *; omega)
  have hUCard : U.card = 2 * m := by omega
  have hVCard : V.card = 2 * m := by omega
  have hUcomp : (Uᶜ).card = 2 * m := by
    have h := card_add_card_compl U
    simp only [Fintype.card_finset, Fintype.card_fin] at h
    omega
  have hVcomp : (Vᶜ).card = 2 * m := by
    have h := card_add_card_compl V
    simp only [Fintype.card_finset, Fintype.card_fin] at h
    omega
  have hI : ((Uᶜ) ∩ (Vᶜ)).card = m := by
    have hs : Uᶜ ∩ Vᶜ = (U ∪ V)ᶜ := by simp
    rw [hs]
    exact hd
  have hEq : (Uᶜ).card * (Vᶜ).card = 2 ^ n * ((Uᶜ) ∩ (Vᶜ)).card := by
    rw [hUcomp, hVcomp, hI, hpow]
    ring
  have hGne : G.Nonempty := card_pos.mp (by rw [hG]; positivity)
  obtain ⟨Y, hY⟩ := hGne
  have hY' := mem_sdiff.mp (hGsub hY)
  obtain ⟨Z, hZV, hZU, hW⟩ := op1370_independent_upper_difference_hub n U V hU hV ⟨Y, hY'.2⟩ ⟨Y, hY'.1⟩ hEq
  refine ⟨Z, ?_, ?_⟩
  · rw [hGC]
    exact mem_sdiff.mpr ⟨hZV, hZU⟩
  · intro X hX
    have hX' : X ∈ C := by simpa [hGC] using hX
    obtain ⟨W, hWV, hWU, hXW, hZW⟩ := hW X (mem_sdiff.mp hX').1 (mem_sdiff.mp hX').2
    refine ⟨W, ?_, hXW, hZW⟩
    rw [hGC]
    exact mem_sdiff.mpr ⟨hWV, hWU⟩
