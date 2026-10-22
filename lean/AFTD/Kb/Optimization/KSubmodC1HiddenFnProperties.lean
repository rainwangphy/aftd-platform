import AFTD.Prelude
import AFTD.Kb.Optimization.IsC1KSubmodKernel
import AFTD.Kb.Optimization.KSubmodHiddenFn
import AFTD.Kb.Optimization.IsKSubmodMonotone
import AFTD.Kb.Optimization.IsKSubmodular
import AFTD.Kb.Optimization.KSubmodC1HiddenFnOrthantDiminishingReturns
import AFTD.Kb.Optimization.KSubmodHiddenFnMonotone
import AFTD.Kb.Optimization.KSubmodularOfMonotoneOfOrthantDiminishingReturns
import AFTD.Kb.Optimization.KSubmodLe
import AFTD.Kb.Optimization.HasOrthantDiminishingReturns
import AFTD.Kb.Optimization.IsKSubmodKernel

/-!
# k_submod_c1_hidden_fn_properties

Topic: submodular   Node: 8e50c7d831d6

Provenance: formalization of a published result. Source: arXiv:2610.26677 Lemma 2.2 -- A Tight Oracle Threshold for k-Submodular Maximization

For all natural numbers n > 0 and k ≥ 2, every hidden label assignment σ : Fin n → Fin k, and every function H : ℝ → ℝ → ℝ satisfying is_c1_k_submod_kernel H, the normalized hidden-label function f = k_submod_hidden_fn H σ satisfies: (1) f x ≥ 0 for all x : Fin n → Option (Fin k); (2) is_k_submod_monotone f; (3) is_k_submodular f; (4) f (fun _ => none) = 0; (5) f x ≤ 1 for all x : Fin n → Option (Fin k); and (6) f (fun e => some (σ e)) = 1.
-/

/-- Monotonicity and k-submodularity of the hidden-label kernel function (Lemma 2.2). -/
theorem k_submod_c1_hidden_fn_properties
    {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (σ : Fin n → Fin k)
    (H : ℝ → ℝ → ℝ) (hH : is_c1_k_submod_kernel H) :
    let f := k_submod_hidden_fn H σ
    (∀ x, 0 ≤ f x) ∧
    is_k_submod_monotone f ∧
    is_k_submodular f ∧
    f (fun _ => none) = 0 ∧
    (∀ x, f x ≤ 1) ∧
    f (fun e => some (σ e)) = 1 := by
  intro f
  have hmono : is_k_submod_monotone f := k_submod_hidden_fn_monotone hn hk σ H hH.2
  have hdim := k_submod_c1_hidden_fn_orthant_diminishing_returns hn hk σ H hH
  have hsubmod : is_k_submodular f := k_submodular_of_monotone_of_orthant_diminishing_returns f hmono hdim
  have hnone : f (fun _ => none) = 0 := by
    dsimp [f, k_submod_hidden_fn]
    have hc : ({e : Fin n | (fun _ : Fin n => (none : Option (Fin k))) e = some (σ e)} : Finset (Fin n)) = ∅ := by
      ext e; simp
    have hm : ({e : Fin n | (fun _ : Fin n => (none : Option (Fin k))) e ≠ none} : Finset (Fin n)) = ∅ := by
      ext e; simp
    rw [hc, hm]
    simp [hH.2.1]
  have hnonneg : ∀ x, 0 ≤ f x := by
    intro x
    have hle : k_submod_le (fun _ => none) x := fun _ => Or.inl rfl
    have := hmono (fun _ => none) x hle
    rwa [hnone] at this
  have hle_one : ∀ x, f x ≤ 1 := by
    intro x
    dsimp [f, k_submod_hidden_fn]
    have hAsubB : ({e : Fin n | x e = some (σ e)} : Finset (Fin n)) ⊆
        ({e : Fin n | x e ≠ none} : Finset (Fin n)) := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      rw [he]; simp
    have hclem : ({e : Fin n | x e = some (σ e)} : Finset (Fin n)).card ≤
        ({e : Fin n | x e ≠ none} : Finset (Fin n)).card := Finset.card_le_card hAsubB
    have hmlen : ({e : Fin n | x e ≠ none} : Finset (Fin n)).card ≤ n := by
      simpa using Finset.card_le_univ ({e : Fin n | x e ≠ none} : Finset (Fin n))
    have hclen : ({e : Fin n | x e = some (σ e)} : Finset (Fin n)).card ≤ n := by
      simpa using Finset.card_le_univ ({e : Fin n | x e = some (σ e)} : Finset (Fin n))
    have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hH10 : (0 : ℝ) < H 1 0 := hH.2.2.1
    have hx0 : 0 ≤ (({e : Fin n | x e = some (σ e)} : Finset (Fin n)).card : ℝ) / (n : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt hnR)
    have hx1 : (({e : Fin n | x e = some (σ e)} : Finset (Fin n)).card : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR]
      exact (Nat.cast_le (α := ℝ)).mpr hclen
    have hy0 : 0 ≤ ((({e : Fin n | x e ≠ none} : Finset (Fin n)).card : ℝ) -
        (({e : Fin n | x e = some (σ e)} : Finset (Fin n)).card : ℝ)) / (n : ℝ) := by
      apply div_nonneg
      · have : (({e : Fin n | x e = some (σ e)} : Finset (Fin n)).card : ℝ) ≤
            (({e : Fin n | x e ≠ none} : Finset (Fin n)).card : ℝ) := (Nat.cast_le (α := ℝ)).mpr hclem
        linarith
      · exact le_of_lt hnR
    have hy1 : ((({e : Fin n | x e ≠ none} : Finset (Fin n)).card : ℝ) -
        (({e : Fin n | x e = some (σ e)} : Finset (Fin n)).card : ℝ)) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR]
      have : (0 : ℝ) ≤ (({e : Fin n | x e = some (σ e)} : Finset (Fin n)).card : ℝ) := Nat.cast_nonneg _
      have : (({e : Fin n | x e ≠ none} : Finset (Fin n)).card : ℝ) ≤ (n : ℝ) := (Nat.cast_le (α := ℝ)).mpr hmlen
      linarith
    have hbound := hH.2.2.2.1 _ _ hx0 hx1 hy0 hy1
    rw [div_le_one hH10]
    exact hbound
  have htop : f (fun e => some (σ e)) = 1 := by
    dsimp [f, k_submod_hidden_fn]
    have hc : ({e : Fin n | (fun e' => some (σ e')) e = some (σ e)} : Finset (Fin n)) = Finset.univ := by
      ext e; simp
    have hm : ({e : Fin n | (fun e' => some (σ e')) e ≠ none} : Finset (Fin n)) = Finset.univ := by
      ext e; simp
    rw [hc, hm]
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
    have hH10 : H 1 0 ≠ 0 := ne_of_gt hH.2.2.1
    simp [Finset.card_univ, Fintype.card_fin, div_self hnR, hH10]
  exact ⟨hnonneg, hmono, hsubmod, hnone, hle_one, htop⟩
