import AFTD.Prelude
import AFTD.Kb.Optimization.IsKSubmodKernel
import AFTD.Kb.Optimization.KSubmodHiddenFn
import AFTD.Kb.Optimization.IsKSubmodMonotone
import AFTD.Kb.Optimization.KSubmodLe

/-!
# k_submod_hidden_fn_monotone

Topic: submodular   Node: edda4d07ac8b

Provenance: helper lemma. arXiv:2610.26677, Lemma 2.2

For n > 0, k ≥ 2, σ : Fin n → Fin k, and H : ℝ → ℝ → ℝ satisfying is_k_submod_kernel, the function k_submod_hidden_fn H σ satisfies is_k_submod_monotone.
-/

/-- The hidden-label function f_σ is monotone. -/
theorem k_submod_hidden_fn_monotone
    {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (σ : Fin n → Fin k)
    (H : ℝ → ℝ → ℝ) (hH : is_k_submod_kernel H) :
    is_k_submod_monotone (k_submod_hidden_fn H σ) := by
  intro x y hxy
  simp only [k_submod_hidden_fn, k_submod_le] at hxy ⊢
  have hAsub : ({e : Fin n | x e = some (σ e)} : Finset (Fin n)) ⊆
      ({e : Fin n | y e = some (σ e)} : Finset (Fin n)) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    rcases hxy e with h | h
    · rw [h] at he; simp at he
    · rw [← h]; exact he
  have hWsub : ({e : Fin n | x e ≠ none ∧ x e ≠ some (σ e)} : Finset (Fin n)) ⊆
      ({e : Fin n | y e ≠ none ∧ y e ≠ some (σ e)} : Finset (Fin n)) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    obtain ⟨hne, hwrong⟩ := he
    rcases hxy e with h | h
    · exact absurd h hne
    · rw [← h]; exact ⟨hne, hwrong⟩
  have hAcard : ({e : Fin n | x e = some (σ e)} : Finset (Fin n)).card ≤
      ({e : Fin n | y e = some (σ e)} : Finset (Fin n)).card := Finset.card_le_card hAsub
  have hWcard : ({e : Fin n | x e ≠ none ∧ x e ≠ some (σ e)} : Finset (Fin n)).card ≤
      ({e : Fin n | y e ≠ none ∧ y e ≠ some (σ e)} : Finset (Fin n)).card := Finset.card_le_card hWsub
  have hAsubB : ({e : Fin n | x e = some (σ e)} : Finset (Fin n)) ⊆
      ({e : Fin n | x e ≠ none} : Finset (Fin n)) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    rw [he]; simp
  have hAsubB' : ({e : Fin n | y e = some (σ e)} : Finset (Fin n)) ⊆
      ({e : Fin n | y e ≠ none} : Finset (Fin n)) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    rw [he]; simp
  have hxsplit : ({e : Fin n | x e ≠ none} : Finset (Fin n)).card -
      ({e : Fin n | x e = some (σ e)} : Finset (Fin n)).card =
      ({e : Fin n | x e ≠ none ∧ x e ≠ some (σ e)} : Finset (Fin n)).card := by
    rw [← Finset.card_sdiff_of_subset hAsubB]
    congr 1
    ext e; simp [Finset.mem_sdiff]
  have hysplit : ({e : Fin n | y e ≠ none} : Finset (Fin n)).card -
      ({e : Fin n | y e = some (σ e)} : Finset (Fin n)).card =
      ({e : Fin n | y e ≠ none ∧ y e ≠ some (σ e)} : Finset (Fin n)).card := by
    rw [← Finset.card_sdiff_of_subset hAsubB']
    congr 1
    ext e; simp [Finset.mem_sdiff]
  have hwx_eq : ((({e : Fin n | x e ≠ none} : Finset (Fin n)).card : ℝ) -
      (({e : Fin n | x e = some (σ e)} : Finset (Fin n)).card : ℝ)) / (n:ℝ) =
      ((({e : Fin n | x e ≠ none ∧ x e ≠ some (σ e)} : Finset (Fin n)).card : ℝ)) / (n:ℝ) := by
    rw [← Nat.cast_sub (Finset.card_le_card hAsubB), hxsplit]
  have hwy_eq : ((({e : Fin n | y e ≠ none} : Finset (Fin n)).card : ℝ) -
      (({e : Fin n | y e = some (σ e)} : Finset (Fin n)).card : ℝ)) / (n:ℝ) =
      ((({e : Fin n | y e ≠ none ∧ y e ≠ some (σ e)} : Finset (Fin n)).card : ℝ)) / (n:ℝ) := by
    rw [← Nat.cast_sub (Finset.card_le_card hAsubB'), hysplit]
  rw [hwx_eq, hwy_eq]
  have hAy_le_n : ({e : Fin n | y e = some (σ e)} : Finset (Fin n)).card ≤ n := by
    simpa using Finset.card_le_univ ({e : Fin n | y e = some (σ e)} : Finset (Fin n))
  have hWx_le_n : ({e : Fin n | x e ≠ none ∧ x e ≠ some (σ e)} : Finset (Fin n)).card ≤ n := by
    simpa using Finset.card_le_univ ({e : Fin n | x e ≠ none ∧ x e ≠ some (σ e)} : Finset (Fin n))
  have hWy_le_n : ({e : Fin n | y e ≠ none ∧ y e ≠ some (σ e)} : Finset (Fin n)).card ≤ n := by
    simpa using Finset.card_le_univ ({e : Fin n | y e ≠ none ∧ y e ≠ some (σ e)} : Finset (Fin n))
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have step1 : H (({e : Fin n | x e = some (σ e)} : Finset (Fin n)).card / (n:ℝ))
      (({e : Fin n | x e ≠ none ∧ x e ≠ some (σ e)} : Finset (Fin n)).card / (n:ℝ)) ≤
      H (({e : Fin n | y e = some (σ e)} : Finset (Fin n)).card / (n:ℝ))
      (({e : Fin n | x e ≠ none ∧ x e ≠ some (σ e)} : Finset (Fin n)).card / (n:ℝ)) := by
    apply hH.2.2.2.1
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hAcard) (Nat.cast_nonneg _)
    · rw [div_le_one hnR]; exact Nat.cast_le.mpr hAy_le_n
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · rw [div_le_one hnR]; exact Nat.cast_le.mpr hWx_le_n
  have step2 : H (({e : Fin n | y e = some (σ e)} : Finset (Fin n)).card / (n:ℝ))
      (({e : Fin n | x e ≠ none ∧ x e ≠ some (σ e)} : Finset (Fin n)).card / (n:ℝ)) ≤
      H (({e : Fin n | y e = some (σ e)} : Finset (Fin n)).card / (n:ℝ))
      (({e : Fin n | y e ≠ none ∧ y e ≠ some (σ e)} : Finset (Fin n)).card / (n:ℝ)) := by
    apply hH.2.2.2.2.1
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · rw [div_le_one hnR]; exact Nat.cast_le.mpr hAy_le_n
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hWcard) (Nat.cast_nonneg _)
    · rw [div_le_one hnR]; exact Nat.cast_le.mpr hWy_le_n
  exact div_le_div_of_nonneg_right (le_trans step1 step2) (le_of_lt hH.2.1)
