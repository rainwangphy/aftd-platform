import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# grid_arrangement_column_deviation_subset_sum_bound

Topic: combinatorics   Node: b2592bdfa10f

Provenance: formalization of a published result. Source: arXiv:2610.38386 Lemma 3.8

Let $n \ge 3$, $N = n^2$, and let $S : \mathrm{Fin}\ n \times \mathrm{Fin}\ n \to \mathbb{Z}$ be an injective arrangement with entries in $\{1, \dots, N\}$. For the column-deviation vector $\gamma_j = \sum_{i=0}^{n-1} S(i,j) - n(N+1)/2$ and any subset of columns $J \subseteq \mathrm{Fin}\ n$ of cardinality $p = |J|$, $|\sum_{j \in J} \gamma_j| \le pn(N-pn)/2$.
-/

lemma grid_arrangement_column_deviation_subset_sum_bound_even_n (n : ℕ) :
    Even ((n : ℤ) * ((n : ℤ) ^ 2 + 1)) := by
  by_cases hn_even : Even (n : ℤ)
  · exact Even.mul_right hn_even _
  · have hodd : Odd (n : ℤ) := by rwa [← Int.not_even_iff_odd]
    have hodd2 : Odd ((n : ℤ) ^ 2) := Odd.pow hodd
    have heven : Even ((n : ℤ) ^ 2 + 1) := Odd.add_odd hodd2 odd_one
    exact Even.mul_left heven _

lemma grid_arrangement_column_deviation_subset_sum_bound_even_E (n p : ℕ) (N : ℤ) (hN : N = (n : ℤ) ^ 2) :
    Even ((p : ℤ) * (n : ℤ) * (N - (p : ℤ) * (n : ℤ))) := by
  have : (p : ℤ) * (n : ℤ) * (N - (p : ℤ) * (n : ℤ)) = (p : ℤ) * ((n : ℤ) - (p : ℤ)) * ((n : ℤ) * (n : ℤ)) := by
    rw [hN]
    ring
  rw [this]
  by_cases hn_even : Even (n : ℤ)
  · have hnn : Even ((n : ℤ) * (n : ℤ)) := Even.mul_left hn_even (n : ℤ)
    exact Even.mul_left hnn _
  · have hodd_n : Odd (n : ℤ) := by rwa [← Int.not_even_iff_odd]
    by_cases hp_even : Even (p : ℤ)
    · have hpn : Even ((p : ℤ) * ((n : ℤ) - (p : ℤ))) := Even.mul_right hp_even _
      exact Even.mul_right hpn _
    · have hodd_p : Odd (p : ℤ) := by rwa [← Int.not_even_iff_odd]
      have he : Even ((n : ℤ) - (p : ℤ)) := Odd.sub_odd hodd_n hodd_p
      have he2 : Even ((p : ℤ) * ((n : ℤ) - (p : ℤ))) := Even.mul_left he _
      exact Even.mul_right he2 _

lemma grid_arrangement_column_deviation_subset_sum_bound_sum_id (M : ℕ) :
    2 * (∑ k ∈ Finset.range M, (k : ℤ)) = (M : ℤ) * ((M : ℤ) - 1) := by
  have h := Finset.sum_range_id_mul_two M
  have hsum : (∑ k ∈ Finset.range M, (k : ℤ)) = ((∑ k ∈ Finset.range M, k : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
  rw [hsum]
  rcases M with _ | M'
  · simp
  · have hsub : M' + 1 - 1 = M' := rfl
    rw [hsub] at h
    have h2' : ((∑ i ∈ Finset.range (M' + 1), i) * 2 : ℤ) = (((M' + 1) * M' : ℕ) : ℤ) := by
      exact_mod_cast h
    push_cast at h2' ⊢
    linear_combination h2'

/-- Majorisation bound for column-deviation subset sums of a grid arrangement (Lemma 3.8, eq. 10). -/
theorem grid_arrangement_column_deviation_subset_sum_bound
    {n : ℕ} (hn : 3 ≤ n) (S : Fin n × Fin n → ℤ)
    (hS_inj : Function.Injective S)
    (hS_range : ∀ c, 1 ≤ S c ∧ S c ≤ (n : ℤ) ^ 2)
    (J : Finset (Fin n)) :
    let γ := fun j => (∑ i : Fin n, S (i, j)) - (n : ℤ) * ((n : ℤ) ^ 2 + 1) / 2
    let p := J.card
    let N := (n : ℤ) ^ 2
    |∑ j ∈ J, γ j| ≤ (p : ℤ) * (n : ℤ) * (N - (p : ℤ) * (n : ℤ)) / 2 := by
  intro γ p N
  set M := p * n
  have hE_n := grid_arrangement_column_deviation_subset_sum_bound_even_n n
  have hdiv_n : 2 * ((n : ℤ) * ((n : ℤ) ^ 2 + 1) / 2) = (n : ℤ) * ((n : ℤ) ^ 2 + 1) := by
    obtain ⟨k, hk⟩ := hE_n; omega
  have h_step1 : 2 * (∑ j ∈ J, γ j) = 2 * (∑ j ∈ J, ∑ i : Fin n, S (i, j)) - (M : ℤ) * (N + 1) := by
    dsimp [γ]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    dsimp [p, N, M]
    calc 2 * (∑ x ∈ J, ∑ i, S (i, x) - (J.card : ℤ) * ((n : ℤ) * ((n : ℤ) ^ 2 + 1) / 2))
      _ = 2 * (∑ x ∈ J, ∑ i, S (i, x)) - (J.card : ℤ) * (2 * ((n : ℤ) * ((n : ℤ) ^ 2 + 1) / 2)) := by ring
      _ = 2 * (∑ x ∈ J, ∑ i, S (i, x)) - (J.card : ℤ) * ((n : ℤ) * ((n : ℤ) ^ 2 + 1)) := by rw [hdiv_n]
      _ = 2 * (∑ j ∈ J, ∑ i, S (i, j)) - (J.card * n : ℤ) * ((n : ℤ) ^ 2 + 1) := by ring
  set A : Finset (Fin n × Fin n) := (Finset.univ : Finset (Fin n)) ×ˢ J
  set s : Finset ℤ := Finset.image S A
  have hA_card : A.card = M := by
    dsimp [A, M, p]
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
  have hs_card : s.card = M := by
    dsimp [s]
    rw [Finset.card_image_of_injective A hS_inj, hA_card]
  have hsum_eq : ∑ j ∈ J, ∑ i : Fin n, S (i, j) = ∑ x ∈ s, x := by
    rw [← Finset.sum_product_right]
    dsimp [s]
    rw [Finset.sum_image]
    intro x _ y _ h
    exact hS_inj h
  have h1 : ∀ x ∈ s, 1 ≤ x := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨c, _, rfl⟩
    exact (hS_range c).1
  have h2 : ∀ x ∈ s, x ≤ N := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨c, _, rfl⟩
    exact (hS_range c).2
  have h_low := Finset.sum_range_le_sum (s := s) (c := 1) h1
  have h_upp := Finset.sum_le_sum_range (s := s) (c := N) h2
  rw [hs_card] at h_low h_upp
  have hsum_id := grid_arrangement_column_deviation_subset_sum_bound_sum_id M
  have h_low_eval : 2 * (∑ k ∈ Finset.range M, (1 + (k : ℤ))) = 2 * (M : ℤ) + (M : ℤ) * ((M : ℤ) - 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    linarith
  have h_upp_eval : 2 * (∑ k ∈ Finset.range M, (N - (k : ℤ))) = 2 * (M : ℤ) * N - (M : ℤ) * ((M : ℤ) - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    linarith
  set T := ∑ x ∈ s, x
  have hT_low : 2 * (M : ℤ) + (M : ℤ) * ((M : ℤ) - 1) ≤ 2 * T := by
    calc 2 * (M : ℤ) + (M : ℤ) * ((M : ℤ) - 1)
      _ = 2 * (∑ k ∈ Finset.range M, (1 + (k : ℤ))) := h_low_eval.symm
      _ ≤ 2 * T := by linarith
  have hT_upp : 2 * T ≤ 2 * (M : ℤ) * N - (M : ℤ) * ((M : ℤ) - 1) := by
    calc 2 * T
      _ ≤ 2 * (∑ k ∈ Finset.range M, (N - (k : ℤ))) := by linarith
      _ = 2 * (M : ℤ) * N - (M : ℤ) * ((M : ℤ) - 1) := h_upp_eval
  set E := (p : ℤ) * (n : ℤ) * (N - (p : ℤ) * (n : ℤ))
  have hM_eq : (M : ℤ) = (p : ℤ) * (n : ℤ) := Nat.cast_mul p n
  have hE_even : Even E := grid_arrangement_column_deviation_subset_sum_bound_even_E n p N rfl
  have h_bound_low : -E ≤ 2 * (∑ j ∈ J, γ j) := by
    rw [h_step1, hsum_eq]
    have hE_id : -E = 2 * (M : ℤ) + (M : ℤ) * ((M : ℤ) - 1) - (M : ℤ) * (N + 1) := by
      rw [hM_eq]
      dsimp [E]
      ring
    rw [hE_id]
    linarith
  have h_bound_upp : 2 * (∑ j ∈ J, γ j) ≤ E := by
    rw [h_step1, hsum_eq]
    have hE_id : E = 2 * (M : ℤ) * N - (M : ℤ) * ((M : ℤ) - 1) - (M : ℤ) * (N + 1) := by
      rw [hM_eq]
      dsimp [E]
      ring
    rw [hE_id]
    linarith
  have hdiv_E : 2 * (E / 2) = E := by
    obtain ⟨k, hk⟩ := hE_even
    omega
  have habs : |2 * (∑ j ∈ J, γ j)| ≤ 2 * (E / 2) := by
    rw [hdiv_E]
    exact abs_le.mpr ⟨h_bound_low, h_bound_upp⟩
  have : |2 * (∑ j ∈ J, γ j)| = 2 * |∑ j ∈ J, γ j| := by
    rw [abs_mul]
    norm_num
  linarith
