import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CooperativeGameCoreNonemptyIffOptimalGuaranteeEqOne

/-!
# cooperative_game_direct_sum_calibration

Topic: general_equilibrium   Node: b4818dcd96ba

Provenance: formalization of a published result. Source: scout/2610-29731-computing-the-nucleon-of-matching-games.md:1148 Lemma 4 (arXiv:2610.29731)

Let (N_1, v_1), ..., (N_m, v_m) (m ≥ 2) be cooperative games with v_j(∅) = 0 and nonnegative values on pairwise disjoint finite player sets, such that W_j = v_j(N_j) > 0 for each j. For each component j, let r_j ∈ (0, 1] be its optimal multiplicative least-core guarantee, meaning there exists a nonnegative vector y on N_j summing to W_j such that y(T) ≥ r_j v_j(T) for all T ⊆ N_j with v_j(T) > 0, and for every nonnegative vector y on N_j summing to W_j there exists T ⊆ N_j with v_j(T) > 0 such that y(T) ≤ r_j v_j(T). Let (N_bar, v_bar) be their direct sum, where N_bar = ⋃_{j=1}^m N_j and v_bar(S) = ∑_{j=1}^m v_j(S ∩ N_j), with grand coalition value W_bar = ∑_{j=1}^m W_j. Then the first-stage optimum of the direct-sum game over all proper coalitions S ⊊ N_bar with v_bar(S) > 0 is α* = W_bar / (∑_{j=1}^m W_j / r_j), meaning there exists a nonnegative vector x on N_bar summing to W_bar such that x(S) ≥ α* v_bar(S) for all proper coalitions S ⊊ N_bar with v_bar(S) > 0, and every nonnegative vector x on N_bar summing to W_bar satisfies x(S) ≤ α* v_bar(S) for some proper coalition S ⊊ N_bar with v_bar(S) > 0. Furthermore, every first-stage optimal imputation x (every nonnegative vector x on N_bar summing to W_bar such that x(S) ≥ α* v_bar(S) for all proper coalitions S ⊊ N_bar with v_bar(S) > 0) assigns component totals ∑_{i ∈ N_j} x(j, i) = α* W_j / r_j for all j. Consequently, α* ≤ 1, with equality if and only if every component has a nonempty core (there exists a nonnegative vector y on N_j summing to W_j such that y(T) ≥ v_j(T) for all T ⊆ N_j).
-/

lemma cooperative_game_direct_sum_calibration_sum_partition {M : Type*} [DecidableEq M] [Fintype M]
    {N : M → Type*} [∀ j, DecidableEq (N j)] [∀ j, Fintype (N j)]
    (S : Finset (Σ j, N j)) (x : (Σ j, N j) → ℝ) :
    S.sum x = Finset.univ.sum (fun j => (Finset.univ.filter (fun (i : N j) => (⟨j, i⟩ : Σ j, N j) ∈ S)).sum (fun i => x ⟨j, i⟩)) := by
  rw [← Finset.sum_ite_mem_eq S x, Fintype.sum_sigma]
  congr 1; ext j
  exact (Finset.sum_filter (fun (i : N j) => (⟨j, i⟩ : Σ j, N j) ∈ S) (fun i => x ⟨j, i⟩)).symm

lemma cooperative_game_direct_sum_calibration_sum_eq_of_le_all {M : Type*} [Fintype M] (s t : M → ℝ)
    (hle : ∀ j, t j ≤ s j) (hsum : Finset.univ.sum s = Finset.univ.sum t) (j : M) :
    s j = t j := by
  have hdiff : Finset.univ.sum (fun k => s k - t k) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hdiff_nonneg : ∀ k ∈ Finset.univ, 0 ≤ s k - t k := fun k _ => sub_nonneg.mpr (hle k)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hdiff_nonneg).mp hdiff j (Finset.mem_univ j)
  exact sub_eq_zero.mp hzero

lemma cooperative_game_direct_sum_calibration_exists_le_of_sum_le {M : Type*} [Fintype M] (hne : Nonempty M) (s t : M → ℝ)
    (hsum : Finset.univ.sum s ≤ Finset.univ.sum t) : ∃ j, s j ≤ t j := by
  by_contra! h
  have : Finset.univ.sum t < Finset.univ.sum s :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => h j)
  linarith

lemma cooperative_game_direct_sum_calibration_v_bar_image {M : Type*} [DecidableEq M] [Fintype M]
    {N : M → Type*} [∀ j, DecidableEq (N j)] [∀ j, Fintype (N j)]
    (v : ∀ j, Finset (N j) → ℝ) (hv_empty : ∀ j, v j ∅ = 0)
    (j : M) (T : Finset (N j)) :
    (Finset.univ.sum (fun k => v k (Finset.univ.filter (fun (i : N k) => (⟨k, i⟩ : Σ j, N j) ∈ T.image (fun i => ⟨j, i⟩))))) = v j T := by
  have h_filter : ∀ k, (Finset.univ.filter (fun (i : N k) => (⟨k, i⟩ : Σ j, N j) ∈ T.image (fun i => ⟨j, i⟩))) =
      if h : k = j then h ▸ T else ∅ := by
    intro k; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    split_ifs with h
    · subst h; simp
    · simp only [Sigma.mk.inj_iff, Finset.notMem_empty, iff_false]
      rintro ⟨a, -, rfl, -⟩; exact h rfl
  simp_rw [h_filter]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · simp
  · intro k _ hk; simp [hk, hv_empty k]

lemma cooperative_game_direct_sum_calibration_image_ne_univ {M : Type*} [DecidableEq M] [Fintype M]
    {N : M → Type*} [∀ j, DecidableEq (N j)] [∀ j, Fintype (N j)]
    (v : ∀ j, Finset (N j) → ℝ) (hm : 2 ≤ Fintype.card M) (hv_empty : ∀ j, v j ∅ = 0)
    (hW : ∀ j, 0 < v j Finset.univ) (j : M) (T : Finset (N j)) :
    (T.image (fun i => (⟨j, i⟩ : Σ j, N j))) ≠ Finset.univ := by
  have : ∃ k : M, k ≠ j := by
    by_contra! h; have : Fintype.card M = 1 := Fintype.card_eq_one_iff.mpr ⟨j, h⟩; omega
  obtain ⟨k, hkj⟩ := this
  have h_ne : Nonempty (N k) := by
    by_contra h_empty; have h_univ : (Finset.univ : Finset (N k)) = ∅ := by ext x; exact (h_empty ⟨x⟩).elim
    have := hW k; rw [h_univ, hv_empty] at this; linarith
  obtain ⟨b⟩ := h_ne; intro h_eq
  have : (⟨k, b⟩ : Σ j, N j) ∈ Finset.univ := Finset.mem_univ _
  rw [← h_eq, Finset.mem_image] at this; obtain ⟨a, -, ha⟩ := this
  have : k = j := (Sigma.mk.inj_iff.mp ha.symm).1; exact hkj this

lemma cooperative_game_direct_sum_calibration_sum_image {M : Type*} [DecidableEq M]
    {N : M → Type*} [∀ j, DecidableEq (N j)]
    (j : M) (T : Finset (N j)) (x : (Σ j, N j) → ℝ) :
    (T.image (fun i => (⟨j, i⟩ : Σ j, N j))).sum x = T.sum (fun i => x ⟨j, i⟩) := by
  apply Finset.sum_image; intro a _ b _ hab; exact (Sigma.mk.inj_iff.mp hab).2.eq

/-- Direct-sum calibration for cooperative games: first-stage optimum and component budgets (arXiv:2610.29731 Lemma 4). -/
theorem cooperative_game_direct_sum_calibration
    {M : Type*} [DecidableEq M] [Fintype M]
    {N : M → Type*} [∀ j, DecidableEq (N j)] [∀ j, Fintype (N j)]
    (v : ∀ j, Finset (N j) → ℝ) (r : M → ℝ)
    (hm : 2 ≤ Fintype.card M)
    (hv_empty : ∀ j, v j ∅ = 0)
    (h_nonneg : ∀ j S, 0 ≤ v j S)
    (hW : ∀ j, 0 < v j Finset.univ)
    (hr_bounds : ∀ j, 0 < r j ∧ r j ≤ 1)
    (hr : ∀ j, (∃ y : N j → ℝ, (∀ i, 0 ≤ y i) ∧ Finset.univ.sum y = v j Finset.univ ∧
      ∀ T : Finset (N j), 0 < v j T → r j * v j T ≤ T.sum y) ∧
      (∀ y : N j → ℝ, (∀ i, 0 ≤ y i) → Finset.univ.sum y = v j Finset.univ →
      ∃ T : Finset (N j), 0 < v j T ∧ T.sum y ≤ r j * v j T)) :
    let W := fun j => v j Finset.univ
    let W_bar := Finset.univ.sum W
    let α_star := W_bar / Finset.univ.sum (fun j => W j / r j)
    let v_bar : Finset (Σ j, N j) → ℝ := fun S => Finset.univ.sum (fun j => v j
      (Finset.univ.filter (fun (i : N j) => (⟨j, i⟩ : Σ j, N j) ∈ S)))
    ((∃ x : (Σ j, N j) → ℝ, (∀ i, 0 ≤ x i) ∧ Finset.univ.sum x = v_bar Finset.univ ∧
      ∀ S : Finset (Σ j, N j), S ≠ Finset.univ → 0 < v_bar S → α_star * v_bar S ≤ S.sum x) ∧
     (∀ x : (Σ j, N j) → ℝ, (∀ i, 0 ≤ x i) → Finset.univ.sum x = v_bar Finset.univ →
      ∃ S : Finset (Σ j, N j), S ≠ Finset.univ ∧ 0 < v_bar S ∧ S.sum x ≤ α_star * v_bar S)) ∧
    (∀ x : (Σ j, N j) → ℝ, (∀ i, 0 ≤ x i) → Finset.univ.sum x = v_bar Finset.univ →
      (∀ S : Finset (Σ j, N j), S ≠ Finset.univ → 0 < v_bar S → α_star * v_bar S ≤ S.sum x) →
      ∀ j : M, Finset.univ.sum (fun a => x ⟨j, a⟩) = α_star * W j / r j) ∧
    α_star ≤ 1 ∧
    (α_star = 1 ↔ ∀ j : M, ∃ y : N j → ℝ, (∀ i, 0 ≤ y i) ∧ Finset.univ.sum y = v j Finset.univ ∧
      ∀ T : Finset (N j), v j T ≤ T.sum y) := by
  intro W W_bar α_star v_bar
  have hM_ne : (Finset.univ : Finset M).Nonempty := by
    rw [Finset.univ_nonempty_iff]; exact Fintype.card_pos_iff.mp (by omega)
  have h_ne : Nonempty M := Fintype.card_pos_iff.mp (by omega)
  have hW_pos : ∀ j, 0 < W j := hW
  have hW_bar_pos : 0 < W_bar := Finset.sum_pos (fun j _ => hW_pos j) hM_ne
  have h_le : ∀ j ∈ (Finset.univ : Finset M), W j ≤ W j / r j := fun j _ => by
    have hrj := hr_bounds j
    have : W j * r j ≤ W j := by nlinarith [hW j]
    exact (le_div_iff₀ hrj.1).mpr this
  have h_sum_le : W_bar ≤ Finset.univ.sum (fun j => W j / r j) := Finset.sum_le_sum h_le
  have h_denom_pos : 0 < Finset.univ.sum (fun j => W j / r j) := by linarith
  have hα_pos : 0 < α_star := div_pos hW_bar_pos h_denom_pos
  have hα_le_one : α_star ≤ 1 := (div_le_one h_denom_pos).mpr h_sum_le
  have hv_univ : v_bar Finset.univ = W_bar := by
    dsimp [v_bar, W_bar, W]
    congr 1; ext j; congr 1; ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  choose y hy_nonneg hy_sum hy_core using (fun j => (hr j).1)
  have hy_core_all : ∀ j T, r j * v j T ≤ T.sum (y j) := by
    intro j T
    by_cases hT : 0 < v j T
    · exact hy_core j T hT
    · have h0 : v j T = 0 := le_antisymm (not_lt.mp hT) (h_nonneg j T)
      rw [h0, mul_zero]
      exact Finset.sum_nonneg (fun i _ => hy_nonneg j i)
  have hx_star : (∃ x : (Σ j, N j) → ℝ, (∀ i, 0 ≤ x i) ∧ Finset.univ.sum x = v_bar Finset.univ ∧
      ∀ S : Finset (Σ j, N j), S ≠ Finset.univ → 0 < v_bar S → α_star * v_bar S ≤ S.sum x) := by
    let x : (Σ j, N j) → ℝ := fun ⟨j, i⟩ => (α_star / r j) * y j i
    refine ⟨x, ?_, ?_, ?_⟩
    · rintro ⟨j, i⟩
      exact mul_nonneg (le_of_lt (div_pos hα_pos (hr_bounds j).1)) (hy_nonneg j i)
    · rw [hv_univ, Fintype.sum_sigma]
      have h1 : ∀ j, Finset.univ.sum (fun i => x ⟨j, i⟩) = (α_star / r j) * W j := by
        intro j
        dsimp [x]
        rw [← Finset.mul_sum, hy_sum]
      have h2 : (fun j => Finset.univ.sum (fun i => x ⟨j, i⟩)) = (fun j => α_star * (W j / r j)) := by
        ext j
        rw [h1]
        ring
      rw [h2, ← Finset.mul_sum]
      exact div_mul_cancel₀ W_bar (ne_of_gt h_denom_pos)
    · intro S _ _
      dsimp [v_bar]
      rw [cooperative_game_direct_sum_calibration_sum_partition S x, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      let Tj := Finset.univ.filter (fun (i : N j) => (⟨j, i⟩ : Σ j, N j) ∈ S)
      have h_scale : Tj.sum (fun i => x ⟨j, i⟩) = (α_star / r j) * Tj.sum (y j) := by
        dsimp [x]
        rw [← Finset.mul_sum]
      rw [h_scale]
      have h_c := hy_core_all j Tj
      have h_pos : 0 ≤ α_star / r j := le_of_lt (div_pos hα_pos (hr_bounds j).1)
      have h_le := mul_le_mul_of_nonneg_left h_c h_pos
      have h_id : (α_star / r j) * (r j * v j Tj) = α_star * v j Tj := by
        rw [← mul_assoc, div_mul_cancel₀ α_star (ne_of_gt (hr_bounds j).1)]
      rwa [h_id] at h_le
  have h_tight : (∀ x : (Σ j, N j) → ℝ, (∀ i, 0 ≤ x i) → Finset.univ.sum x = v_bar Finset.univ →
      ∃ S : Finset (Σ j, N j), S ≠ Finset.univ ∧ 0 < v_bar S ∧ S.sum x ≤ α_star * v_bar S) := by
    intro x hx_nonneg hx_sum
    let s : M → ℝ := fun j => Finset.univ.sum (fun a => x ⟨j, a⟩)
    let t : M → ℝ := fun j => α_star * W j / r j
    have hs_sum : Finset.univ.sum s = W_bar := by
      rw [← Fintype.sum_sigma]
      exact hx_sum.trans hv_univ
    have ht_sum : Finset.univ.sum t = W_bar := by
      have h1 : (fun j => α_star * W j / r j) = (fun j => α_star * (W j / r j)) := by
        ext j; ring
      dsimp [t]
      rw [h1, ← Finset.mul_sum]
      exact div_mul_cancel₀ W_bar (ne_of_gt h_denom_pos)
    have h_exist : ∃ j, s j ≤ t j := by
      apply cooperative_game_direct_sum_calibration_exists_le_of_sum_le h_ne
      rw [hs_sum, ht_sum]
    obtain ⟨j, hj_le⟩ := h_exist
    have hs_nonneg : 0 ≤ s j := Finset.sum_nonneg (fun i _ => hx_nonneg ⟨j, i⟩)
    by_cases hs_zero : s j = 0
    · let S : Finset (Σ j, N j) := Finset.univ.image (fun i => ⟨j, i⟩)
      have hvS : v_bar S = W j := cooperative_game_direct_sum_calibration_v_bar_image v hv_empty j Finset.univ
      have hSx : S.sum x = s j := cooperative_game_direct_sum_calibration_sum_image j Finset.univ x
      refine ⟨S, ?_, ?_, ?_⟩
      · exact cooperative_game_direct_sum_calibration_image_ne_univ v hm hv_empty hW j Finset.univ
      · rw [hvS]; exact hW_pos j
      · rw [hvS, hSx, hs_zero]
        exact mul_nonneg (le_of_lt hα_pos) (le_of_lt (hW_pos j))
    · have hs_pos : 0 < s j := lt_of_le_of_ne hs_nonneg (Ne.symm hs_zero)
      let y_scaled : N j → ℝ := fun a => (W j / s j) * x ⟨j, a⟩
      have hy_scaled_nonneg : ∀ i, 0 ≤ y_scaled i := fun i =>
        mul_nonneg (div_nonneg (le_of_lt (hW_pos j)) (le_of_lt hs_pos)) (hx_nonneg ⟨j, i⟩)
      have hy_scaled_sum : Finset.univ.sum y_scaled = v j Finset.univ := by
        dsimp [y_scaled]
        rw [← Finset.mul_sum]
        have : Finset.univ.sum (fun a => x ⟨j, a⟩) = s j := rfl
        rw [this, div_mul_cancel₀ (W j) (ne_of_gt hs_pos)]
      obtain ⟨T, hT_pos, hT_le⟩ := (hr j).2 y_scaled hy_scaled_nonneg hy_scaled_sum
      let S : Finset (Σ j, N j) := T.image (fun i => ⟨j, i⟩)
      have hvS : v_bar S = v j T := cooperative_game_direct_sum_calibration_v_bar_image v hv_empty j T
      have hSx : S.sum x = T.sum (fun a => x ⟨j, a⟩) := cooperative_game_direct_sum_calibration_sum_image j T x
      refine ⟨S, ?_, ?_, ?_⟩
      · exact cooperative_game_direct_sum_calibration_image_ne_univ v hm hv_empty hW j T
      · rw [hvS]; exact hT_pos
      · rw [hvS, hSx]
        have h_scale : T.sum (fun a => x ⟨j, a⟩) = (s j / W j) * T.sum y_scaled := by
          dsimp [y_scaled]
          rw [← Finset.mul_sum]
          have h_cancel : (s j / W j) * (W j / s j) = 1 := by
            rw [div_mul_div_comm, mul_comm (s j), div_self (ne_of_gt (mul_pos (hW_pos j) hs_pos))]
          rw [← mul_assoc, h_cancel, one_mul]
        rw [h_scale]
        have h_step1 : (s j / W j) * T.sum y_scaled ≤ (s j / W j) * (r j * v j T) :=
          mul_le_mul_of_nonneg_left hT_le (div_nonneg (le_of_lt hs_pos) (le_of_lt (hW_pos j)))
        have h_step2 : (s j / W j) * (r j * v j T) ≤ α_star * v j T := by
          have hrj := (hr_bounds j).1
          have hWj := hW_pos j
          have : (s j / W j) * (r j * v j T) = (s j * r j / W j) * v j T := by ring
          rw [this]
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hT_pos)
          have hj_le' : s j ≤ α_star * W j / r j := hj_le
          rw [div_le_iff₀ hWj]
          have : s j * r j ≤ α_star * W j := by
            have : s j * r j ≤ (α_star * W j / r j) * r j :=
              mul_le_mul_of_nonneg_right hj_le' (le_of_lt hrj)
            rwa [div_mul_cancel₀ (α_star * W j) (ne_of_gt hrj)] at this
          exact this
        exact le_trans h_step1 h_step2
  have h_unique : (∀ x : (Σ j, N j) → ℝ, (∀ i, 0 ≤ x i) → Finset.univ.sum x = v_bar Finset.univ →
      (∀ S : Finset (Σ j, N j), S ≠ Finset.univ → 0 < v_bar S → α_star * v_bar S ≤ S.sum x) →
      ∀ j : M, Finset.univ.sum (fun a => x ⟨j, a⟩) = α_star * W j / r j) := by
    intro x hx_nonneg hx_sum h_core
    let s : M → ℝ := fun j => Finset.univ.sum (fun a => x ⟨j, a⟩)
    let t : M → ℝ := fun j => α_star * W j / r j
    have hs_sum : Finset.univ.sum s = W_bar := by
      rw [← Fintype.sum_sigma]
      exact hx_sum.trans hv_univ
    have ht_sum : Finset.univ.sum t = W_bar := by
      have h1 : (fun j => α_star * W j / r j) = (fun j => α_star * (W j / r j)) := by
        ext j; ring
      dsimp [t]
      rw [h1, ← Finset.mul_sum]
      exact div_mul_cancel₀ W_bar (ne_of_gt h_denom_pos)
    have h_le_each : ∀ j, t j ≤ s j := by
      intro j
      have hs_nonneg : 0 ≤ s j := Finset.sum_nonneg (fun i _ => hx_nonneg ⟨j, i⟩)
      by_cases hs_zero : s j = 0
      · exfalso
        let Suniv : Finset (Σ j, N j) := Finset.univ.image (fun i => ⟨j, i⟩)
        have hS_ne : Suniv ≠ Finset.univ := cooperative_game_direct_sum_calibration_image_ne_univ v hm hv_empty hW j Finset.univ
        have hvS : v_bar Suniv = W j := cooperative_game_direct_sum_calibration_v_bar_image v hv_empty j Finset.univ
        have hS_pos : 0 < v_bar Suniv := by rw [hvS]; exact hW_pos j
        have h_bound := h_core Suniv hS_ne hS_pos
        have hSx : Suniv.sum x = s j := cooperative_game_direct_sum_calibration_sum_image j Finset.univ x
        rw [hvS, hSx, hs_zero] at h_bound
        have : 0 < α_star * W j := mul_pos hα_pos (hW_pos j)
        linarith
      · have hs_pos : 0 < s j := lt_of_le_of_ne hs_nonneg (Ne.symm hs_zero)
        let y_scaled : N j → ℝ := fun a => (W j / s j) * x ⟨j, a⟩
        have hy_scaled_nonneg : ∀ i, 0 ≤ y_scaled i := fun i =>
          mul_nonneg (div_nonneg (le_of_lt (hW_pos j)) (le_of_lt hs_pos)) (hx_nonneg ⟨j, i⟩)
        have hy_scaled_sum : Finset.univ.sum y_scaled = v j Finset.univ := by
          dsimp [y_scaled]
          rw [← Finset.mul_sum]
          have : Finset.univ.sum (fun a => x ⟨j, a⟩) = s j := rfl
          rw [this, div_mul_cancel₀ (W j) (ne_of_gt hs_pos)]
        obtain ⟨T, hT_pos, hT_le⟩ := (hr j).2 y_scaled hy_scaled_nonneg hy_scaled_sum
        let S : Finset (Σ j, N j) := T.image (fun i => ⟨j, i⟩)
        have hS_ne : S ≠ Finset.univ := cooperative_game_direct_sum_calibration_image_ne_univ v hm hv_empty hW j T
        have hvS : v_bar S = v j T := cooperative_game_direct_sum_calibration_v_bar_image v hv_empty j T
        have hS_pos : 0 < v_bar S := by rw [hvS]; exact hT_pos
        have h_bound := h_core S hS_ne hS_pos
        have hSx : S.sum x = T.sum (fun a => x ⟨j, a⟩) := cooperative_game_direct_sum_calibration_sum_image j T x
        rw [hvS, hSx] at h_bound
        have h_scale : T.sum (fun a => x ⟨j, a⟩) = (s j / W j) * T.sum y_scaled := by
          dsimp [y_scaled]
          rw [← Finset.mul_sum]
          have h_cancel : (s j / W j) * (W j / s j) = 1 := by
            rw [div_mul_div_comm, mul_comm (s j), div_self (ne_of_gt (mul_pos (hW_pos j) hs_pos))]
          rw [← mul_assoc, h_cancel, one_mul]
        have h_step1 : T.sum (fun a => x ⟨j, a⟩) ≤ (s j / W j) * (r j * v j T) := by
          rw [h_scale]
          exact mul_le_mul_of_nonneg_left hT_le (div_nonneg (le_of_lt hs_pos) (le_of_lt (hW_pos j)))
        have h_chain : α_star * v j T ≤ (s j * r j / W j) * v j T := by
          have : (s j / W j) * (r j * v j T) = (s j * r j / W j) * v j T := by ring
          linarith
        have h_div : α_star ≤ s j * r j / W j := (mul_le_mul_iff_of_pos_right hT_pos).mp h_chain
        dsimp [t]
        have hrj := (hr_bounds j).1
        have hWj := hW_pos j
        have : α_star * W j ≤ s j * r j := (le_div_iff₀ hWj).mp h_div
        exact (div_le_iff₀ hrj).mpr (by linarith)
    intro j
    exact cooperative_game_direct_sum_calibration_sum_eq_of_le_all s t h_le_each (hs_sum.trans ht_sum.symm) j
  have h_core_iff : ∀ j, (r j = 1 ↔ ∃ y : N j → ℝ, (∀ i, 0 ≤ y i) ∧ Finset.univ.sum y = v j Finset.univ ∧
      ∀ T : Finset (N j), v j T ≤ T.sum y) := by
    intro j
    exact cooperative_game_core_nonempty_iff_optimal_guarantee_eq_one (v j) (r j)
      (h_nonneg j) (hW j) (hr_bounds j) (hr j)
  have h_α_iff : (α_star = 1 ↔ ∀ j, r j = 1) := by
    have h_diff_nonneg : ∀ j ∈ (Finset.univ : Finset M), 0 ≤ W j / r j - W j :=
      fun j hj => sub_nonneg.mpr (h_le j hj)
    constructor
    · intro hα
      have h_eq : Finset.univ.sum (fun j => W j / r j) = W_bar :=
        ((div_eq_one_iff_eq (ne_of_gt h_denom_pos)).mp hα).symm
      have h_sum_diff : Finset.univ.sum (fun j => W j / r j - W j) = 0 := by
        rw [Finset.sum_sub_distrib]
        change Finset.univ.sum (fun j => W j / r j) - W_bar = 0
        rw [h_eq, sub_self]
      have h_each_zero := (Finset.sum_eq_zero_iff_of_nonneg h_diff_nonneg).mp h_sum_diff
      intro j
      have hj := h_each_zero j (Finset.mem_univ j)
      have : W j / r j = W j := sub_eq_zero.mp hj
      have hrj := (hr_bounds j).1
      have h_mul : W j / r j * r j = W j * r j := by rw [this]
      rw [div_mul_cancel₀ (W j) (ne_of_gt hrj)] at h_mul
      nlinarith [hW_pos j]
    · intro hr_one
      have h_denom_eq : Finset.univ.sum (fun j => W j / r j) = W_bar := by
        dsimp [W_bar, W]
        congr 1; ext j
        rw [hr_one j, div_one]
      dsimp [α_star]
      rw [h_denom_eq]
      exact div_self (ne_of_gt hW_bar_pos)
  refine ⟨⟨hx_star, h_tight⟩, h_unique, hα_le_one, ?_⟩
  rw [h_α_iff]
  exact forall_congr' h_core_iff
