import AFTD.Prelude
import AFTD.Kb.Optimization.IsC1KSubmodKernel
import AFTD.Kb.Optimization.KSubmodHiddenFn
import AFTD.Kb.Optimization.HasOrthantDiminishingReturns
import AFTD.Kb.Optimization.KSubmodLe
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Optimization.IsKSubmodKernel
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal
import AFTD.Kb.Tcs.G

/-!
# k_submod_c1_hidden_fn_orthant_diminishing_returns

Topic: submodular   Node: f4059b1d5c7d

Provenance: helper lemma. arXiv:2610.26677, proof of Lemma 2.2, Eq. (7)

For all natural numbers n > 0 and k ≥ 2, every hidden assignment σ : Fin n → Fin k, and every function H : ℝ → ℝ → ℝ satisfying is_c1_k_submod_kernel H, the normalized hidden-label function k_submod_hidden_fn H σ satisfies has_orthant_diminishing_returns.
-/

lemma k_submod_c1_deriv_fst_comp (H : ℝ → ℝ → ℝ) (hH : ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2))
    (c w t : ℝ) :
    deriv (fun t => H (c + t) w) t = deriv (fun s => H s w) (c + t) := by
  have hd_g : DifferentiableAt ℝ (fun s => H s w) (c + t) := by
    have hd : Differentiable ℝ (fun p : ℝ × ℝ => H p.1 p.2) := hH.differentiable (by norm_num)
    have : (fun s => H s w) = (fun p : ℝ × ℝ => H p.1 p.2) ∘ (fun s => (s, w)) := rfl
    rw [this]
    exact (hd (c + t, w)).comp (c + t) ((differentiable_id.prodMk (differentiable_const w)) (c + t))
  have hd_f : DifferentiableAt ℝ (fun t => c + t) t :=
    (differentiable_const c |>.add differentiable_id).differentiableAt
  have hcomp : (fun t => H (c + t) w) = (fun s => H s w) ∘ (fun t => c + t) := rfl
  rw [hcomp, deriv_comp t hd_g hd_f]
  have hf' : deriv (fun t => c + t) t = 1 := by simp
  rw [hf', mul_one]

lemma k_submod_c1_diff_fst_comp (H : ℝ → ℝ → ℝ) (hH : ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2))
    (c w : ℝ) :
    Differentiable ℝ (fun t => H (c + t) w) := by
  have hd : Differentiable ℝ (fun p : ℝ × ℝ => H p.1 p.2) := hH.differentiable (by norm_num)
  have h_comp : (fun t => H (c + t) w) = (fun p : ℝ × ℝ => H p.1 p.2) ∘ (fun t => (c + t, w)) := rfl
  rw [h_comp]
  apply Differentiable.comp hd
  exact (differentiable_const c |>.add differentiable_id).prodMk (differentiable_const w)

lemma k_submod_c1_kernel_diminishing_fst (H : ℝ → ℝ → ℝ) (hH : is_c1_k_submod_kernel H)
    {cx cy wx wy h : ℝ} (h_cx : 0 ≤ cx) (hc : cx ≤ cy) (h_cy : cy + h ≤ 1)
    (h_wx : 0 ≤ wx) (hw : wx ≤ wy) (h_wy : wy ≤ 1) (hh : 0 ≤ h) :
    H (cy + h) wy - H cy wy ≤ H (cx + h) wx - H cx wx := by
  rcases hH.2 with ⟨h00, h10, hbound, hmono1, hmono2, hderiv1, hderiv2⟩
  let g : ℝ → ℝ := fun t => H (cx + t) wx - H (cy + t) wy
  have hg_diff : Differentiable ℝ g :=
    (k_submod_c1_diff_fst_comp H hH.1 cx wx).sub (k_submod_c1_diff_fst_comp H hH.1 cy wy)
  have hg_mono : MonotoneOn g (Set.Icc 0 h) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 h) hg_diff.continuous.continuousOn
      hg_diff.differentiableOn
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have hth : t ≤ h := le_of_lt ht.2
    change 0 ≤ deriv ((fun t => H (cx + t) wx) - (fun t => H (cy + t) wy)) t
    rw [deriv_sub (k_submod_c1_diff_fst_comp H hH.1 cx wx).differentiableAt
                  (k_submod_c1_diff_fst_comp H hH.1 cy wy).differentiableAt,
        k_submod_c1_deriv_fst_comp H hH.1 cx wx t,
        k_submod_c1_deriv_fst_comp H hH.1 cy wy t]
    have h_le := hderiv1 (cx + t) (cy + t) wx wy
      (by linarith) (by linarith) (by linarith) h_wx hw h_wy
    linarith
  have h0_mem : (0 : ℝ) ∈ Set.Icc 0 h := Set.left_mem_Icc.mpr hh
  have hh_mem : h ∈ Set.Icc 0 h := Set.right_mem_Icc.mpr hh
  have := hg_mono h0_mem hh_mem hh
  dsimp [g] at this
  simp only [add_zero] at this
  linarith

lemma k_submod_c1_deriv_snd_comp (H : ℝ → ℝ → ℝ) (hH : ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2))
    (c w t : ℝ) :
    deriv (fun t => H c (w + t)) t = deriv (fun s => H c s) (w + t) := by
  have hd_g : DifferentiableAt ℝ (fun s => H c s) (w + t) := by
    have hd : Differentiable ℝ (fun p : ℝ × ℝ => H p.1 p.2) := hH.differentiable (by norm_num)
    have : (fun s => H c s) = (fun p : ℝ × ℝ => H p.1 p.2) ∘ (fun s => (c, s)) := rfl
    rw [this]
    exact (hd (c, w + t)).comp (w + t) (((differentiable_const c).prodMk differentiable_id) (w + t))
  have hd_f : DifferentiableAt ℝ (fun t => w + t) t :=
    (differentiable_const w |>.add differentiable_id).differentiableAt
  have hcomp : (fun t => H c (w + t)) = (fun s => H c s) ∘ (fun t => w + t) := rfl
  rw [hcomp, deriv_comp t hd_g hd_f]
  have hf' : deriv (fun t => w + t) t = 1 := by simp
  rw [hf', mul_one]

lemma k_submod_c1_diff_snd_comp (H : ℝ → ℝ → ℝ) (hH : ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2))
    (c w : ℝ) :
    Differentiable ℝ (fun t => H c (w + t)) := by
  have hd : Differentiable ℝ (fun p : ℝ × ℝ => H p.1 p.2) := hH.differentiable (by norm_num)
  have h_comp : (fun t => H c (w + t)) = (fun p : ℝ × ℝ => H p.1 p.2) ∘ (fun t => (c, w + t)) := rfl
  rw [h_comp]
  apply Differentiable.comp hd
  exact (differentiable_const c).prodMk (differentiable_const w |>.add differentiable_id)

lemma k_submod_c1_kernel_diminishing_snd (H : ℝ → ℝ → ℝ) (hH : is_c1_k_submod_kernel H)
    {cx cy wx wy h : ℝ} (h_cx : 0 ≤ cx) (hc : cx ≤ cy) (h_cy : cy ≤ 1)
    (h_wx : 0 ≤ wx) (hw : wx ≤ wy) (h_wy : wy + h ≤ 1) (hh : 0 ≤ h) :
    H cy (wy + h) - H cy wy ≤ H cx (wx + h) - H cx wx := by
  rcases hH.2 with ⟨h00, h10, hbound, hmono1, hmono2, hderiv1, hderiv2⟩
  let g : ℝ → ℝ := fun t => H cx (wx + t) - H cy (wy + t)
  have hg_diff : Differentiable ℝ g :=
    (k_submod_c1_diff_snd_comp H hH.1 cx wx).sub (k_submod_c1_diff_snd_comp H hH.1 cy wy)
  have hg_mono : MonotoneOn g (Set.Icc 0 h) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 h) hg_diff.continuous.continuousOn
      hg_diff.differentiableOn
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have hth : t ≤ h := le_of_lt ht.2
    change 0 ≤ deriv ((fun t => H cx (wx + t)) - (fun t => H cy (wy + t))) t
    rw [deriv_sub (k_submod_c1_diff_snd_comp H hH.1 cx wx).differentiableAt
                  (k_submod_c1_diff_snd_comp H hH.1 cy wy).differentiableAt,
        k_submod_c1_deriv_snd_comp H hH.1 cx wx t,
        k_submod_c1_deriv_snd_comp H hH.1 cy wy t]
    have h_le := hderiv2 cx cy (wx + t) (wy + t)
      h_cx hc h_cy (by linarith) (by linarith) (by linarith)
    linarith
  have h0_mem : (0 : ℝ) ∈ Set.Icc 0 h := Set.left_mem_Icc.mpr hh
  have hh_mem : h ∈ Set.Icc 0 h := Set.right_mem_Icc.mpr hh
  have := hg_mono h0_mem hh_mem hh
  dsimp [g] at this
  simp only [add_zero] at this
  linarith

lemma k_submod_c1_card_sub_eq_wrong {n k : ℕ} (z : Fin n → Option (Fin k)) (σ : Fin n → Fin k) :
    (({e : Fin n | z e ≠ none} : Finset (Fin n)).card : ℝ) -
    (({e : Fin n | z e = some (σ e)} : Finset (Fin n)).card : ℝ) =
    (({e : Fin n | z e ≠ none ∧ z e ≠ some (σ e)} : Finset (Fin n)).card : ℝ) := by
  have hAsubB : ({e : Fin n | z e = some (σ e)} : Finset (Fin n)) ⊆
      ({e : Fin n | z e ≠ none} : Finset (Fin n)) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    rw [he]; simp
  have hzsplit : ({e : Fin n | z e ≠ none} : Finset (Fin n)).card -
      ({e : Fin n | z e = some (σ e)} : Finset (Fin n)).card =
      ({e : Fin n | z e ≠ none ∧ z e ≠ some (σ e)} : Finset (Fin n)).card := by
    rw [← Finset.card_sdiff_of_subset hAsubB]
    congr 1
    ext e; simp [Finset.mem_sdiff]
  rw [← Nat.cast_sub (Finset.card_le_card hAsubB), hzsplit]

lemma k_submod_c1_hidden_fn_eq {n k : ℕ} (H : ℝ → ℝ → ℝ) (σ : Fin n → Fin k)
    (z : Fin n → Option (Fin k)) :
    k_submod_hidden_fn H σ z =
      H (({e : Fin n | z e = some (σ e)} : Finset (Fin n)).card / (n : ℝ))
        (({e : Fin n | z e ≠ none ∧ z e ≠ some (σ e)} : Finset (Fin n)).card / (n : ℝ)) / H 1 0 := by
  dsimp [k_submod_hidden_fn]
  rw [k_submod_c1_card_sub_eq_wrong]

lemma k_submod_c1_card_add_one_le_n_of_not_mem {n : ℕ} (S : Finset (Fin n)) (e : Fin n) (he : e ∉ S) :
    S.card + 1 ≤ n := by
  have : (insert e S).card ≤ Fintype.card (Fin n) := Finset.card_le_univ (insert e S)
  rw [Finset.card_insert_of_notMem he, Fintype.card_fin] at this
  exact this

lemma k_submod_c1_card_update_eq_sigma_card {n k : ℕ} (z : Fin n → Option (Fin k)) (σ : Fin n → Fin k)
    (e : Fin n) (he : z e = none) :
    (({j : Fin n | Function.update z e (some (σ e)) j = some (σ j)} : Finset (Fin n)).card =
      ({j : Fin n | z j = some (σ j)} : Finset (Fin n)).card + 1) ∧
    (({j : Fin n | Function.update z e (some (σ e)) j ≠ none ∧
                  Function.update z e (some (σ e)) j ≠ some (σ j)} : Finset (Fin n)).card =
      ({j : Fin n | z j ≠ none ∧ z j ≠ some (σ j)} : Finset (Fin n)).card) := by
  have hC : ({j : Fin n | Function.update z e (some (σ e)) j = some (σ j)} : Finset (Fin n)) =
      insert e ({j : Fin n | z j = some (σ j)} : Finset (Fin n)) := by
    ext j
    by_cases h : j = e
    · subst h; simp [Function.update_self]
    · simp [h]
  have hW : ({j : Fin n | Function.update z e (some (σ e)) j ≠ none ∧
                        Function.update z e (some (σ e)) j ≠ some (σ j)} : Finset (Fin n)) =
      ({j : Fin n | z j ≠ none ∧ z j ≠ some (σ j)} : Finset (Fin n)) := by
    ext j
    by_cases h : j = e
    · subst h; simp [Function.update_self, he]
    · simp [Function.update_of_ne h]
  have hnot : e ∉ ({j : Fin n | z j = some (σ j)} : Finset (Fin n)) := by simp [he]
  constructor
  · rw [hC, Finset.card_insert_of_notMem hnot]
  · rw [hW]

lemma k_submod_c1_card_update_ne_sigma_card {n k : ℕ} (z : Fin n → Option (Fin k)) (σ : Fin n → Fin k)
    (e : Fin n) (i : Fin k) (he : z e = none) (hi : i ≠ σ e) :
    (({j : Fin n | Function.update z e (some i) j = some (σ j)} : Finset (Fin n)).card =
      ({j : Fin n | z j = some (σ j)} : Finset (Fin n)).card) ∧
    (({j : Fin n | Function.update z e (some i) j ≠ none ∧
                  Function.update z e (some i) j ≠ some (σ j)} : Finset (Fin n)).card =
      ({j : Fin n | z j ≠ none ∧ z j ≠ some (σ j)} : Finset (Fin n)).card + 1) := by
  have hC : ({j : Fin n | Function.update z e (some i) j = some (σ j)} : Finset (Fin n)) =
      ({j : Fin n | z j = some (σ j)} : Finset (Fin n)) := by
    ext j
    by_cases h : j = e
    · subst h; simp [Function.update_self, he, hi]
    · simp [h]
  have hW : ({j : Fin n | Function.update z e (some i) j ≠ none ∧
                        Function.update z e (some i) j ≠ some (σ j)} : Finset (Fin n)) =
      insert e ({j : Fin n | z j ≠ none ∧ z j ≠ some (σ j)} : Finset (Fin n)) := by
    ext j
    by_cases h : j = e
    · subst h; simp [Function.update_self, hi]
    · simp [h]
  have hnot : e ∉ ({j : Fin n | z j ≠ none ∧ z j ≠ some (σ j)} : Finset (Fin n)) := by simp [he]
  constructor
  · rw [hC]
  · rw [hW, Finset.card_insert_of_notMem hnot]

lemma k_submod_c1_sub_div_le_sub_div {A B C D K : ℝ} (h : A - B ≤ C - D) (hK : 0 < K) :
    A / K - B / K ≤ C / K - D / K := by
  rw [← sub_div, ← sub_div]
  exact div_le_div_of_nonneg_right h (le_of_lt hK)

/-- Orthant diminishing returns for the hidden-label function constructed from a C^1 kernel. -/
theorem k_submod_c1_hidden_fn_orthant_diminishing_returns
    {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (σ : Fin n → Fin k)
    (H : ℝ → ℝ → ℝ) (hH : is_c1_k_submod_kernel H) :
    has_orthant_diminishing_returns (k_submod_hidden_fn H σ) := by
  intro x y e i hxy hye
  have hxe : x e = none := by
    rcases hxy e with h | h
    · exact h
    · rw [h, hye]
  have hAsub : ({j : Fin n | x j = some (σ j)} : Finset (Fin n)) ⊆
      ({j : Fin n | y j = some (σ j)} : Finset (Fin n)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rcases hxy j with h | h
    · rw [h] at hj; simp at hj
    · rw [← h]; exact hj
  have hWsub : ({j : Fin n | x j ≠ none ∧ x j ≠ some (σ j)} : Finset (Fin n)) ⊆
      ({j : Fin n | y j ≠ none ∧ y j ≠ some (σ j)} : Finset (Fin n)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    obtain ⟨hne, hwrong⟩ := hj
    rcases hxy j with h | h
    · exact absurd h hne
    · rw [← h]; exact ⟨hne, hwrong⟩
  have hCy_not_mem : e ∉ ({j : Fin n | y j = some (σ j)} : Finset (Fin n)) := by simp [hye]
  have hWy_not_mem : e ∉ ({j : Fin n | y j ≠ none ∧ y j ≠ some (σ j)} : Finset (Fin n)) := by simp [hye]
  have hCy_add1 : ({j : Fin n | y j = some (σ j)} : Finset (Fin n)).card + 1 ≤ n :=
    k_submod_c1_card_add_one_le_n_of_not_mem _ _ hCy_not_mem
  have hWy_add1 : ({j : Fin n | y j ≠ none ∧ y j ≠ some (σ j)} : Finset (Fin n)).card + 1 ≤ n :=
    k_submod_c1_card_add_one_le_n_of_not_mem _ _ hWy_not_mem
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set cx := (({j : Fin n | x j = some (σ j)} : Finset (Fin n)).card : ℝ) / (n : ℝ)
  set cy := (({j : Fin n | y j = some (σ j)} : Finset (Fin n)).card : ℝ) / (n : ℝ)
  set wx := (({j : Fin n | x j ≠ none ∧ x j ≠ some (σ j)} : Finset (Fin n)).card : ℝ) / (n : ℝ)
  set wy := (({j : Fin n | y j ≠ none ∧ y j ≠ some (σ j)} : Finset (Fin n)).card : ℝ) / (n : ℝ)
  have hcx_nonneg : 0 ≤ cx := div_nonneg (Nat.cast_nonneg _) (le_of_lt hnR)
  have hwx_nonneg : 0 ≤ wx := div_nonneg (Nat.cast_nonneg _) (le_of_lt hnR)
  have hc_le : cx ≤ cy := div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hAsub)) (le_of_lt hnR)
  have hw_le : wx ≤ wy := div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hWsub)) (le_of_lt hnR)
  have hcy_le1 : cy ≤ 1 := by
    rw [div_le_one hnR]
    exact Nat.cast_le.mpr (by linarith [hCy_add1])
  have hwy_le1 : wy ≤ 1 := by
    rw [div_le_one hnR]
    exact Nat.cast_le.mpr (by linarith [hWy_add1])
  have hh_nonneg : 0 ≤ (1 : ℝ) / (n : ℝ) := div_nonneg zero_le_one (le_of_lt hnR)
  by_cases hi : i = σ e
  · subst hi
    obtain ⟨hCy', hWy'⟩ := k_submod_c1_card_update_eq_sigma_card y σ e hye
    obtain ⟨hCx', hWx'⟩ := k_submod_c1_card_update_eq_sigma_card x σ e hxe
    rw [k_submod_c1_hidden_fn_eq H σ (Function.update y e (some (σ e))),
        k_submod_c1_hidden_fn_eq H σ y,
        k_submod_c1_hidden_fn_eq H σ (Function.update x e (some (σ e))),
        k_submod_c1_hidden_fn_eq H σ x]
    rw [hCy', hWy', hCx', hWx']
    have hcast_y : (((({j : Fin n | y j = some (σ j)} : Finset (Fin n)).card + 1 : ℕ) : ℝ) / (n : ℝ)) =
        cy + 1 / (n : ℝ) := by
      push_cast; ring
    have hcast_x : (((({j : Fin n | x j = some (σ j)} : Finset (Fin n)).card + 1 : ℕ) : ℝ) / (n : ℝ)) =
        cx + 1 / (n : ℝ) := by
      push_cast; ring
    rw [hcast_y, hcast_x]
    have hcy_h : cy + 1 / (n : ℝ) ≤ 1 := by
      rw [← hcast_y, div_le_one hnR]
      exact Nat.cast_le.mpr hCy_add1
    have hdim := k_submod_c1_kernel_diminishing_fst H hH
      hcx_nonneg hc_le hcy_h hwx_nonneg hw_le hwy_le1 hh_nonneg
    exact k_submod_c1_sub_div_le_sub_div hdim hH.2.2.1
  · obtain ⟨hCy', hWy'⟩ := k_submod_c1_card_update_ne_sigma_card y σ e i hye hi
    obtain ⟨hCx', hWx'⟩ := k_submod_c1_card_update_ne_sigma_card x σ e i hxe hi
    rw [k_submod_c1_hidden_fn_eq H σ (Function.update y e (some i)),
        k_submod_c1_hidden_fn_eq H σ y,
        k_submod_c1_hidden_fn_eq H σ (Function.update x e (some i)),
        k_submod_c1_hidden_fn_eq H σ x]
    rw [hCy', hWy', hCx', hWx']
    have hcast_y : (((({j : Fin n | y j ≠ none ∧ y j ≠ some (σ j)} : Finset (Fin n)).card + 1 : ℕ) : ℝ) / (n : ℝ)) =
        wy + 1 / (n : ℝ) := by
      push_cast; ring
    have hcast_x : (((({j : Fin n | x j ≠ none ∧ x j ≠ some (σ j)} : Finset (Fin n)).card + 1 : ℕ) : ℝ) / (n : ℝ)) =
        wx + 1 / (n : ℝ) := by
      push_cast; ring
    rw [hcast_y, hcast_x]
    have hwy_h : wy + 1 / (n : ℝ) ≤ 1 := by
      rw [← hcast_y, div_le_one hnR]
      exact Nat.cast_le.mpr hWy_add1
    have hdim := k_submod_c1_kernel_diminishing_snd H hH
      hcx_nonneg hc_le hcy_le1 hwx_nonneg hw_le hwy_h hh_nonneg
    exact k_submod_c1_sub_div_le_sub_div hdim hH.2.2.1
