import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralMooreMaxOrder
import AFTD.Kb.Tcs.SpectralMooreSeidelSwitch
import AFTD.Kb.Tcs.SpectralMooreSeidelSwitchDegreeSumGe
import AFTD.Kb.Tcs.SpectralMooreSeidelSwitchAdjQuadformLe
import AFTD.Kb.Tcs.SpectralMooreSecondEigenvalueLe

/-!
# spectral_moore_max_order_le_of_large_degree_of_switch_degree_bounds

Topic: graphs   Node: c2863531a20b

Provenance: helper lemma. arXiv:2611.00591 (A spectral Moore problem and the Yang-Koolen conjecture), proof of Theorem 5.4 (from Lemmas 5.1-5.3)

Let θ ≥ 1. Suppose (i) there are D, N₀ such that every k-regular graph G on Fin n with second largest adjacency eigenvalue at most θ, 2k + 2 ≤ n and N₀ ≤ n has a Seidel switching spectral_moore_seidel_switch G X of maximum degree at most D; and (ii) for every d0 and ε > 0 there is N such that every graph F on Fin n with n ≥ N, maximum degree at most d0, and x ⬝ᵥ (F.adjMatrix ℝ *ᵥ x) ≤ θ * (x ⬝ᵥ x) for all x : Fin n → ℝ with ∑ x = 0, has ∑ v, F.degree v ≤ n (1 + θ²/4 + ε). Then there is K with spectral_moore_max_order k θ ≤ 2k + 2⌊1 + θ²/4⌋₊ for every k ≥ K.
-/

open Classical SimpleGraph Matrix in
theorem spectral_moore_max_order_le_of_large_degree_of_switch_degree_bounds (θ : ℝ) (hθ : 1 ≤ θ)
    (hswitch : ∃ D N₀ : ℕ, ∀ (n k : ℕ) (G : SimpleGraph (Fin n)), G.IsRegularOfDegree k →
      spectral_moore_second_eigenvalue_le G θ → 2 * k + 2 ≤ n → N₀ ≤ n →
      ∃ X : Set (Fin n), ∀ v, (spectral_moore_seidel_switch G X).degree v ≤ D)
    (hdeg : ∀ (d0 : ℕ) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ (n : ℕ) (F : SimpleGraph (Fin n)), N ≤ n →
      (∀ v, F.degree v ≤ d0) →
      (∀ x : Fin n → ℝ, ∑ i, x i = 0 → x ⬝ᵥ (F.adjMatrix ℝ *ᵥ x) ≤ θ * (x ⬝ᵥ x)) →
      ∑ v, (F.degree v : ℝ) ≤ n * (1 + θ ^ 2 / 4 + ε)) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      spectral_moore_max_order k θ ≤ ((2 * k + 2 * ⌊1 + θ ^ 2 / 4⌋₊ : ℕ) : ℕ∞) := by
  obtain ⟨D, N₀, hsw⟩ := hswitch
  set L := ⌊1 + θ ^ 2 / 4⌋₊ with hLdef
  have hC0 : (0 : ℝ) ≤ 1 + θ ^ 2 / 4 := by positivity
  have hL1 : (L : ℝ) ≤ 1 + θ ^ 2 / 4 := Nat.floor_le hC0
  have hL2 : 1 + θ ^ 2 / 4 < L + 1 := Nat.lt_floor_add_one _
  have hLpos : 1 ≤ L := by
    rw [hLdef]; exact Nat.le_floor (by norm_num; positivity)
  set ε : ℝ := (L + 1 - (1 + θ ^ 2 / 4)) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set δ : ℝ := L + 1 - (1 + θ ^ 2 / 4) - ε with hδ
  have hδpos : 0 < δ := by rw [hδ, hε]; linarith
  obtain ⟨N, hN⟩ := hdeg D ε hεpos
  refine ⟨N + N₀ + D + 1 + ⌈2 * (D : ℝ) ^ 2 / δ⌉₊, fun k hk => ?_⟩
  unfold spectral_moore_max_order
  refine iSup_le fun n => iSup_le fun G => iSup_le fun hG => ?_
  obtain ⟨_, hreg, hlam⟩ := hG
  rw [Nat.cast_le]
  by_contra hlt
  push Not at hlt
  have hn2 : 2 * k + 2 ≤ n := by omega
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  obtain ⟨X, hX⟩ := hsw n k G hreg hlam hn2 (by omega)
  have hDk : D < k := by omega
  have hsum := spectral_moore_seidel_switch_degree_sum_ge G X k D hreg hDk hX (by rw [hcard]; exact hn2)
  rw [hcard] at hsum
  have hkθ : (k : ℝ) ≤ θ + (Fintype.card (Fin n) : ℝ) / 2 := by
    rw [hcard]
    have : (2 * k + 2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hq := spectral_moore_seidel_switch_adj_quadform_le G X k θ hreg hlam hkθ
  have hup := hN n (spectral_moore_seidel_switch G X) (by omega) hX hq
  have hc : L + 1 ≤ (n - 2 * k + 1) / 2 := by omega
  have hcr : ((L : ℝ) + 1) ≤ (((n - 2 * k + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hc
  have hsumr : (n : ℝ) * (((n - 2 * k + 1) / 2 : ℕ) : ℝ) ≤
      ∑ v, ((spectral_moore_seidel_switch G X).degree v : ℝ) + 2 * (D : ℝ) ^ 2 := by
    exact_mod_cast hsum
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have h1 : (n : ℝ) * (L + 1) ≤ n * (1 + θ ^ 2 / 4 + ε) + 2 * (D : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hcr hn0
    linarith
  have hnK : (⌈2 * (D : ℝ) ^ 2 / δ⌉₊ : ℝ) < n := by
    have : ⌈2 * (D : ℝ) ^ 2 / δ⌉₊ < n := by omega
    exact_mod_cast this
  have h2 : 2 * (D : ℝ) ^ 2 / δ < n := lt_of_le_of_lt (Nat.le_ceil _) hnK
  rw [div_lt_iff₀ hδpos] at h2
  have : (n : ℝ) * δ ≤ 2 * (D : ℝ) ^ 2 := by rw [hδ]; linarith
  linarith
