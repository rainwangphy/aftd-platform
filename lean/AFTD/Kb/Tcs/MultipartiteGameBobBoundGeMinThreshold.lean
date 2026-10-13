import AFTD.Prelude

/-!
# multipartite_game_bob_bound_ge_min_threshold

Topic: combinatorics   Node: 40360e19f638

Provenance: formalization of a published result. Source: arXiv:2610.12508 (The Game Chromatic Number of Complete Multipartite Graphs with Triples), Lemma 3.2.

Let A ≥ 1, D ≥ 3 and r₁ ≥ r₂ ≥ … ≥ r_D ≥ 4 be integers, R_j = r₁ + … + r_j, P = A + Σ_{i=1}^{D} ⌈r_i/2⌉ and F_{D−2} = 2A + 1 + ⌈max(R_{D−2} − A + 1, 0)/2⌉. Then A + ⌊(A + R_{D−1} + 1)/2⌋ ≥ min(F_{D−2}, P). (Natural-number division: ⌈x/2⌉ = (x+1)/2, and the truncated R + 1 − A is max(R − A + 1, 0).)
-/

lemma multipartite_game_bob_bound_sum_icc_decomp_three (D : ℕ) (hD : 3 ≤ D) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.Icc 1 D, f i =
      (∑ i ∈ Finset.Icc 1 (D - 3), f i) + f (D - 2) + f (D - 1) + f D := by
  have h1 : D = (D - 1) + 1 := by omega
  have ha1 : 1 ≤ (D - 1) + 1 := by omega
  have h2 : D - 1 = (D - 2) + 1 := by omega
  have ha2 : 1 ≤ (D - 2) + 1 := by omega
  have h3 : D - 2 = (D - 3) + 1 := by omega
  have ha3 : 1 ≤ (D - 3) + 1 := by omega
  nth_rw 1 [h1]
  rw [Finset.sum_Icc_succ_top ha1]
  nth_rw 1 [h2]
  rw [Finset.sum_Icc_succ_top ha2]
  nth_rw 1 [h3]
  rw [Finset.sum_Icc_succ_top ha3]
  rw [← h3, ← h2, ← h1]

lemma multipartite_game_bob_bound_sum_icc_decomp_two (D : ℕ) (hD : 3 ≤ D) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.Icc 1 (D - 1), f i =
      (∑ i ∈ Finset.Icc 1 (D - 3), f i) + f (D - 2) + f (D - 1) := by
  have h2 : D - 1 = (D - 2) + 1 := by omega
  have ha2 : 1 ≤ (D - 2) + 1 := by omega
  have h3 : D - 2 = (D - 3) + 1 := by omega
  have ha3 : 1 ≤ (D - 3) + 1 := by omega
  nth_rw 1 [h2]
  rw [Finset.sum_Icc_succ_top ha2]
  nth_rw 1 [h3]
  rw [Finset.sum_Icc_succ_top ha3]
  rw [← h3, ← h2]

lemma multipartite_game_bob_bound_sum_icc_decomp_one (D : ℕ) (hD : 3 ≤ D) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.Icc 1 (D - 1), f i =
      (∑ i ∈ Finset.Icc 1 (D - 2), f i) + f (D - 1) := by
  have h2 : D - 1 = (D - 2) + 1 := by omega
  have ha2 : 1 ≤ (D - 2) + 1 := by omega
  nth_rw 1 [h2]
  rw [Finset.sum_Icc_succ_top ha2]
  rw [← h2]

lemma multipartite_game_bob_bound_sum_div_two_le_sum (D : ℕ) (r : ℕ → ℕ) (hD : 3 ≤ D)
    (hmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ D → r j ≤ r i) (h4 : 4 ≤ r D) :
    ∑ i ∈ Finset.Icc 1 D, (r i + 1) / 2 ≤ ∑ i ∈ Finset.Icc 1 (D - 1), r i := by
  rw [multipartite_game_bob_bound_sum_icc_decomp_three D hD (fun i => (r i + 1) / 2)]
  rw [multipartite_game_bob_bound_sum_icc_decomp_two D hD r]
  have hsum : ∑ i ∈ Finset.Icc 1 (D - 3), (r i + 1) / 2 ≤ ∑ i ∈ Finset.Icc 1 (D - 3), r i := by
    apply Finset.sum_le_sum
    intro i _
    omega
  have hrD_le_rD1 : r D ≤ r (D - 1) := hmono (D - 1) D (by omega) (by omega) (by omega)
  have hrD1_le_rD2 : r (D - 1) ≤ r (D - 2) := hmono (D - 2) (D - 1) (by omega) (by omega) (by omega)
  omega

theorem multipartite_game_bob_bound_ge_min_threshold (A D : ℕ) (r : ℕ → ℕ) (hA : 1 ≤ A)
    (hD : 3 ≤ D) (hmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ D → r j ≤ r i) (h4 : 4 ≤ r D) :
    min (2 * A + 1 + ((∑ i ∈ Finset.Icc 1 (D - 2), r i) + 1 - A + 1) / 2)
        (A + ∑ i ∈ Finset.Icc 1 D, (r i + 1) / 2) ≤
      A + (A + ∑ i ∈ Finset.Icc 1 (D - 1), r i + 1) / 2 := by
  have _ := hA
  have hrD1 : 4 ≤ r (D - 1) := by
    have : r D ≤ r (D - 1) := hmono (D - 1) D (by omega) (by omega) (by omega)
    omega
  have hdecomp : ∑ i ∈ Finset.Icc 1 (D - 1), r i =
      (∑ i ∈ Finset.Icc 1 (D - 2), r i) + r (D - 1) :=
    multipartite_game_bob_bound_sum_icc_decomp_one D hD r
  by_cases h : A + 1 ≤ ∑ i ∈ Finset.Icc 1 (D - 1), r i
  · apply le_trans (min_le_left _ _)
    rw [hdecomp] at h ⊢
    omega
  · apply le_trans (min_le_right _ _)
    have hsum : ∑ i ∈ Finset.Icc 1 D, (r i + 1) / 2 ≤ ∑ i ∈ Finset.Icc 1 (D - 1), r i :=
      multipartite_game_bob_bound_sum_div_two_le_sum D r hD hmono h4
    omega
