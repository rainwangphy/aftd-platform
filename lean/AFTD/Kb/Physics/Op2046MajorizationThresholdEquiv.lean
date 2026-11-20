import AFTD.Prelude
import AFTD.Kb.Physics.Op2046Majorizes
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op2046_majorization_threshold_equiv

Topic: quantum_mechanics   Node: 7fff6ebbe872

Provenance: helper lemma. Deterministic reduction for OP-2046 via positive-part transforms of finite spectra.

For finite real vectors with positive sums, normalized majorization is equivalent to dominance of the sums of positive parts above every real threshold.
-/

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section

theorem op2046_majorization_threshold_equiv (n : ℕ) (x y : Fin n → ℝ) (hx : 0 < ∑ i, x i) (hy : 0 < ∑ i, y i) : op2046_majorizes n x y ↔ ∀ s : ℝ, (∑ i, max (y i / (∑ j, y j) - s) 0) ≤ ∑ i, max (x i / (∑ j, x j) - s) 0 := by
  constructor
  · intro h s
    let v := fun i => y i / (∑ j, y j)
    let u := fun i => x i / (∑ j, x j)
    let T := Finset.filter (fun i => s < v i) Finset.univ
    have hT_sum : (∑ i, max (v i - s) 0) = (∑ i ∈ T, (v i - s)) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => s < v i)]
      have h1 : ∀ i ∈ T, max (v i - s) 0 = v i - s := by
        intro i hi
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact max_eq_left (sub_nonneg.mpr (le_of_lt hi))
      have h2 : ∀ i ∈ Finset.filter (fun i => ¬(s < v i)) Finset.univ, max (v i - s) 0 = 0 := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact max_eq_right (sub_nonpos.mpr (not_lt.mp hi))
      rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero, add_zero]
    obtain ⟨S, hScard, hSineq⟩ := h.2.2 T
    have hT_expand : (∑ i ∈ T, (v i - s)) = (∑ i ∈ T, v i) - (T.card : ℝ) * s := by
      simp [Finset.sum_sub_distrib]
    have hS_expand : (∑ i ∈ S, (u i - s)) = (∑ i ∈ S, u i) - (S.card : ℝ) * s := by
      simp [Finset.sum_sub_distrib]
    have h_sum_T_eq : (∑ i ∈ T, v i) = (∑ i ∈ T, y i) / (∑ j, y j) :=
      (Finset.sum_div T y (∑ j, y j)).symm
    have h_sum_S_eq : (∑ i ∈ S, u i) = (∑ i ∈ S, x i) / (∑ j, x j) :=
      (Finset.sum_div S x (∑ j, x j)).symm
    have h_le : (∑ i ∈ T, v i) - (T.card : ℝ) * s ≤ (∑ i ∈ S, u i) - (S.card : ℝ) * s := by
      rw [h_sum_T_eq, h_sum_S_eq, hScard]
      linarith
    have hS_le : (∑ i ∈ S, (u i - s)) ≤ ∑ i, max (u i - s) 0 := by
      have h1 : (∑ i ∈ S, (u i - s)) ≤ ∑ i ∈ S, max (u i - s) 0 :=
        Finset.sum_le_sum (fun i _ => le_max_left (u i - s) 0)
      have h2 : (∑ i ∈ S, max (u i - s) 0) ≤ ∑ i, max (u i - s) 0 :=
        Finset.sum_le_univ_sum_of_nonneg (fun i => le_max_right (u i - s) 0)
      exact le_trans h1 h2
    rw [hT_sum, hT_expand]
    rw [← hS_expand] at h_le
    exact le_trans h_le hS_le
  · intro h_thresh
    refine ⟨hx, hy, fun T => ?_⟩
    by_cases hT0 : T.card = 0
    · use ∅
      rw [Finset.card_eq_zero.mp hT0]
      simp
    · have hk0 : 0 < T.card := Nat.pos_of_ne_zero hT0
      have hkn : T.card ≤ n := by
        have := Finset.card_le_univ T
        simpa using this
      let u := fun i => x i / (∑ j, x j)
      let v := fun i => y i / (∑ j, y j)
      let σ := Tuple.sort (-u)
      let g := u ∘ σ
      have hg : Antitone g := by
        intro i j hij
        have h := Tuple.monotone_sort (-u) hij
        have h' : - u (σ i) ≤ - u (σ j) := h
        dsimp [g]
        linarith
      let m : Fin n := ⟨T.card - 1, by omega⟩
      let s := g m
      let I := Finset.filter (fun i : Fin n => (i : ℕ) < T.card) Finset.univ
      have hIcard : I.card = T.card := by
        have : I = Finset.image (fun (i : Fin T.card) => (⟨i.val, Nat.lt_of_lt_of_le i.isLt hkn⟩ : Fin n)) Finset.univ := by
          ext ⟨x, hx_lt⟩
          simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro h
            exact ⟨⟨x, h⟩, rfl⟩
          · rintro ⟨⟨y, hy⟩, hy2⟩
            cases hy2
            exact hy
        rw [this, Finset.card_image_of_injective]
        · simp
        · intro ⟨a, ha⟩ ⟨b, hb⟩ h
          ext
          exact Fin.mk.inj h
      let S := Finset.image σ I
      have hScard : S.card = T.card := by
        rw [Finset.card_image_of_injective _ (fun _ _ h => σ.injective h), hIcard]
      use S
      refine ⟨hScard, ?_⟩
      have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => (i : ℕ) < T.card)
        (fun i => max (g i - s) 0)).symm
      have h1 : ∀ i ∈ I, max (g i - s) 0 = g i - s := by
        intro i hi
        simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        have him : i ≤ m := by
          rw [Fin.le_def]
          dsimp [m]
          omega
        have hgi : s ≤ g i := hg him
        exact max_eq_left (sub_nonneg.mpr hgi)
      have h2 : ∀ i ∈ Finset.filter (fun i : Fin n => ¬((i : ℕ) < T.card)) Finset.univ, max (g i - s) 0 = 0 := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        have hmi : m ≤ i := by
          rw [Fin.le_def]
          dsimp [m]
          omega
        have hgi : g i ≤ s := hg hmi
        exact max_eq_right (sub_nonpos.mpr hgi)
      have hg_sum : (∑ i, max (g i - s) 0) = ∑ i ∈ I, (g i - s) := by
        rw [hsplit, Finset.sum_congr rfl h1]
        have h2' : (∑ i ∈ Finset.filter (fun i : Fin n => ¬((i : ℕ) < T.card)) Finset.univ, max (g i - s) 0) = 0 := by
          rw [Finset.sum_congr rfl h2, Finset.sum_const_zero]
        rw [h2', add_zero]
      have h_u_sum : (∑ i, max (u i - s) 0) = ∑ i, max (g i - s) 0 := by
        have := (Equiv.sum_comp σ (fun j => max (u j - s) 0)).symm
        exact this
      have hS_sum : (∑ i ∈ S, u i) = ∑ i ∈ I, g i := by
        exact Finset.sum_image (fun _ _ _ _ h => σ.injective h)
      have hI_expand : (∑ i ∈ I, (g i - s)) = (∑ i ∈ I, g i) - (T.card : ℝ) * s := by
        simp [Finset.sum_sub_distrib, hIcard]
      have h_u_final : (∑ i, max (u i - s) 0) = (∑ i ∈ S, u i) - (T.card : ℝ) * s := by
        rw [h_u_sum, hg_sum, hI_expand, ← hS_sum]
      have hT_le : (∑ i ∈ T, v i) - (T.card : ℝ) * s ≤ ∑ i, max (v i - s) 0 := by
        have hT_sub : (∑ i ∈ T, (v i - s)) = (∑ i ∈ T, v i) - (T.card : ℝ) * s := by
          simp [Finset.sum_sub_distrib]
        rw [← hT_sub]
        have h1 : (∑ i ∈ T, (v i - s)) ≤ ∑ i ∈ T, max (v i - s) 0 :=
          Finset.sum_le_sum (fun i _ => le_max_left (v i - s) 0)
        have h2 : (∑ i ∈ T, max (v i - s) 0) ≤ ∑ i, max (v i - s) 0 :=
          Finset.sum_le_univ_sum_of_nonneg (fun i => le_max_right (v i - s) 0)
        exact le_trans h1 h2
      have h_main : (∑ i ∈ T, v i) - (T.card : ℝ) * s ≤ (∑ i ∈ S, u i) - (T.card : ℝ) * s := by
        have h_th := h_thresh s
        exact le_trans (le_trans hT_le h_th) (le_of_eq h_u_final)
      have h_le : (∑ i ∈ T, v i) ≤ (∑ i ∈ S, u i) := by
        linarith
      have h_sum_T_eq : (∑ i ∈ T, v i) = (∑ i ∈ T, y i) / (∑ j, y j) :=
        (Finset.sum_div T y (∑ j, y j)).symm
      have h_sum_S_eq : (∑ i ∈ S, u i) = (∑ i ∈ S, x i) / (∑ j, x j) :=
        (Finset.sum_div S x (∑ j, x j)).symm
      rw [← h_sum_T_eq, ← h_sum_S_eq]
      exact h_le
