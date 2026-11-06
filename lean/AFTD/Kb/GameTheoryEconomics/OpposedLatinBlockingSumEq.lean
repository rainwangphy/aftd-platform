import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OpposedLatinMarket
import AFTD.Kb.GameTheoryEconomics.IsBlockingPair
import AFTD.Kb.Tcs.LatinSquareIs

/-!
# opposed_latin_blocking_sum_eq

Topic: matching_markets   Node: 37802aad819c

Provenance: formalization of a published result. Source: arXiv:2609.17418 (A Quadratic Lower Bound for the Shield Number of the Stable Marriage Problem), eq. (2), Lemma 2.1 and Remark 3.3: E[B] = (1/(n(n-1))) sum_ij A_ij B_ij, computed there for the cyclic market C_n; here for every opposed Latin market, where A_ij = n-1-L(i,j) and B_ij = L(i,j). Stated as a sum over matchings in natural numbers.

Let n >= 2 and let L be an n x n Latin square with symbols 0,...,n-1 (every row and every column of L is a permutation). In the opposed Latin marriage market of L (man i ranks woman j at position L(i,j)+1, woman j ranks man i at position n-L(i,j), smaller rank preferred), let B(mu) be the number of blocking pairs of a complete matching mu. Then the sum of B(mu) over all n! complete matchings mu is n! * n(n-2)/6; that is, the expected number of blocking pairs of a uniformly random complete matching is exactly n(n-2)/6.
-/

theorem opposed_latin_blocking_sum_eq (n : ℕ) (hn : 2 ≤ n) (L : Fin n → Fin n → Fin n)
    (hL : latin_square_is L) :
    6 * ∑ μ : Equiv.Perm (Fin n),
        {p : Fin n × Fin n | is_blocking_pair (opposed_latin_market L) μ p.1 p.2}.ncard =
      n.factorial * (n * (n - 2)) := by
  classical
  obtain ⟨hrow, hcol⟩ := hL
  have key : ∀ (G : Fin n → Fin n → ℕ) (i k : Fin n), i ≠ k →
      n * (n - 1) * ∑ μ : Equiv.Perm (Fin n), G (μ i) (μ k) =
        n.factorial * ∑ a : Fin n, ∑ b : Fin n, if a = b then 0 else G a b := by
    intro G i k hik
    classical
    have inv : ∀ i' k' : Fin n, i' ≠ k' →
        ∑ μ : Equiv.Perm (Fin n), G (μ i') (μ k') = ∑ μ : Equiv.Perm (Fin n), G (μ i) (μ k) := by
      intro i' k' hik'
      obtain ⟨ρ, h1, h2⟩ : ∃ ρ : Equiv.Perm (Fin n), ρ i = i' ∧ ρ k = k' := by
        set σ := Equiv.swap i i' with hσ
        have hm : σ k ≠ i' := by
          intro h
          apply hik
          apply σ.injective
          rw [h, hσ, Equiv.swap_apply_left]
        refine ⟨Equiv.swap (σ k) k' * σ, ?_, ?_⟩
        · rw [Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_left]
          exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hm) hik'
        · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      symm
      rw [← Equiv.sum_comp (Equiv.mulRight ρ)]
      simp [Equiv.Perm.mul_apply, h1, h2]
    have hcard : ∀ i' : Fin n, (∑ k' : Fin n, if i' = k' then 0 else 1) = n - 1 := by
      intro i'
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.filter_ne, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
    have hsum : ∑ i' : Fin n, ∑ k' : Fin n,
        (if i' = k' then 0 else ∑ μ : Equiv.Perm (Fin n), G (μ i') (μ k')) =
          n * (n - 1) * ∑ μ : Equiv.Perm (Fin n), G (μ i) (μ k) := by
      have : ∀ i' k' : Fin n, (if i' = k' then 0 else ∑ μ : Equiv.Perm (Fin n), G (μ i') (μ k')) =
          (if i' = k' then 0 else 1) * ∑ μ : Equiv.Perm (Fin n), G (μ i) (μ k) := by
        intro i' k'
        split_ifs with h
        · simp
        · rw [one_mul, inv i' k' h]
      simp only [this, ← Finset.sum_mul, hcard, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    rw [← hsum]
    have hswap : ∀ μ : Equiv.Perm (Fin n),
        (∑ i' : Fin n, ∑ k' : Fin n, if i' = k' then 0 else G (μ i') (μ k')) =
          ∑ a : Fin n, ∑ b : Fin n, if a = b then 0 else G a b := by
      intro μ
      rw [← Equiv.sum_comp μ (fun a => ∑ b : Fin n, if a = b then 0 else G a b)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Equiv.sum_comp μ (fun b => if μ a = b then 0 else G (μ a) b)]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [μ.injective.eq_iff]
    have hcomm : (∑ i' : Fin n, ∑ k' : Fin n,
        (if i' = k' then 0 else ∑ μ : Equiv.Perm (Fin n), G (μ i') (μ k'))) =
        ∑ μ : Equiv.Perm (Fin n), ∑ i' : Fin n, ∑ k' : Fin n,
          if i' = k' then 0 else G (μ i') (μ k') := by
      have hpush : ∀ i' k' : Fin n,
          (if i' = k' then 0 else ∑ μ : Equiv.Perm (Fin n), G (μ i') (μ k')) =
            ∑ μ : Equiv.Perm (Fin n), if i' = k' then 0 else G (μ i') (μ k') := by
        intro i' k'
        split_ifs <;> simp
      simp_rw [hpush]
      rw [Finset.sum_congr rfl fun i' _ => Finset.sum_comm]
      exact Finset.sum_comm
    rw [hcomm, Finset.sum_congr rfl fun μ _ => hswap μ, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
  have hf : ∀ m : ℕ, 6 * ∑ y ∈ Finset.range m, (m - 1 - y) * y = m * (m - 1) * (m - 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h : ∑ y ∈ Finset.range (n + 1), (n + 1 - 1 - y) * y =
          ∑ y ∈ Finset.range n, (n - 1 - y) * y + ∑ y ∈ Finset.range n, y := by
        rw [Finset.sum_range_succ, ← Finset.sum_add_distrib]
        simp only [Nat.add_sub_cancel, Nat.sub_self, zero_mul, add_zero]
        refine Finset.sum_congr rfl fun y hy => ?_
        have := Finset.mem_range.mp hy
        obtain ⟨d, rfl⟩ : ∃ d, n = y + 1 + d := ⟨n - y - 1, by omega⟩
        rw [show y + 1 + d - y = d + 1 by omega, show y + 1 + d - 1 - y = d by omega]
        ring
      have g := Finset.sum_range_id_mul_two n
      rw [h, mul_add, ih]
      rcases n with _ | _ | n
      · simp
      · simp
      · have e1 : n + 1 + 1 + 1 - 2 = n + 1 := by omega
        have e2 : n + 1 + 1 - 2 = n := by omega
        have : 6 * ∑ i ∈ Finset.range (n + 1 + 1), i = 3 * ((n + 1 + 1) * (n + 1)) := by
          rw [show (n + 1 + 1) * (n + 1) = (∑ i ∈ Finset.range (n + 1 + 1), i) * 2 by
            rw [g]; rfl]; ring
        rw [this]
        simp only [Nat.add_sub_cancel, e1, e2]
        ring
  set G : Fin n → Fin n → Fin n → Fin n → ℕ := fun i k a b =>
    if (L i b : ℕ) < L i a ∧ (L k b : ℕ) < L i b then 1 else 0 with hG
  have hB : ∀ μ : Equiv.Perm (Fin n),
      {p : Fin n × Fin n | is_blocking_pair (opposed_latin_market L) μ p.1 p.2}.ncard =
        ∑ i : Fin n, ∑ k : Fin n, G i k (μ i) (μ k) := by
    intro μ
    have hset : {p : Fin n × Fin n | is_blocking_pair (opposed_latin_market L) μ p.1 p.2} =
        ↑(Finset.univ.filter fun p : Fin n × Fin n =>
          (L p.1 p.2 : ℕ) < L p.1 (μ p.1) ∧ (L (μ.symm p.2) p.2 : ℕ) < L p.1 p.2) := by
      ext p
      simp only [is_blocking_pair, opposed_latin_market, Set.mem_ofPred_eq, Finset.coe_filter,
        Finset.mem_univ, true_and]
      have := (L p.1 p.2).isLt
      have := (L (μ.symm p.2) p.2).isLt
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
    rw [hset, Set.ncard_coe_finset, Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp μ (fun j => if (L i j : ℕ) < L i (μ i) ∧ (L (μ.symm j) j : ℕ) < L i j
      then 1 else 0)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hG]
  have hdiag : ∀ i a b : Fin n, G i i a b = 0 := by
    intro i a b; simp only [hG]; split_ifs with h <;> omega
  have hstep : n * (n - 1) * ∑ μ : Equiv.Perm (Fin n), ∑ i : Fin n, ∑ k : Fin n,
      G i k (μ i) (μ k) =
        n.factorial * ∑ i : Fin n, ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          (if a = b then 0 else G i k a b) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hik : i = k
    · subst hik
      simp [hdiag]
    · exact key (G i k) i k hik
  have hrowsum : ∀ (i : Fin n) (x : ℕ),
      (∑ a : Fin n, if x < (L i a : ℕ) then 1 else 0) = n - 1 - x := by
    intro i x
    rw [← Equiv.sum_comp (Equiv.ofBijective _ (hrow i).bijective_of_finite).symm]
    simp only [Equiv.ofBijective_apply_symm_apply]
    rw [Fin.sum_univ_eq_sum_range (fun y => if x < y then 1 else 0) n, Finset.sum_boole,
      Nat.cast_id, show (Finset.range n).filter (fun y => x < y) = Finset.Ioo x n by
        ext y; simp [Finset.mem_Ioo]; omega, Nat.card_Ioo]
    omega
  have hcolsum : ∀ (b : Fin n) (x : ℕ), x ≤ n →
      (∑ k : Fin n, if (L k b : ℕ) < x then 1 else 0) = x := by
    intro b x hx
    rw [← Equiv.sum_comp (Equiv.ofBijective (fun i => L i b) (hcol b).bijective_of_finite).symm]
    have h := fun y => Equiv.ofBijective_apply_symm_apply (fun i => L i b)
      (hcol b).bijective_of_finite y
    simp only [h]
    rw [Fin.sum_univ_eq_sum_range (fun y => if y < x then 1 else 0) n, Finset.sum_boole,
      Nat.cast_id, show (Finset.range n).filter (fun y => y < x) = Finset.range x by
        ext y; simp; omega, Finset.card_range]
  have hT : ∑ i : Fin n, ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n,
      (if a = b then 0 else G i k a b) = n * ∑ y ∈ Finset.range n, (n - 1 - y) * y := by
    have hrow' : ∀ i : Fin n, (∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n,
        (if a = b then 0 else G i k a b)) = ∑ y ∈ Finset.range n, (n - 1 - y) * y := by
      intro i
      have e1 : ∀ k a b : Fin n, (if a = b then 0 else G i k a b) =
          (if (L i b : ℕ) < L i a then 1 else 0) * (if (L k b : ℕ) < L i b then 1 else 0) := by
        intro k a b
        simp only [hG]
        by_cases hab : a = b
        · subst hab; simp
        · rw [if_neg hab]
          by_cases h1 : (L i b : ℕ) < L i a <;> by_cases h2 : (L k b : ℕ) < L i b <;> simp [h1, h2]
      simp_rw [e1]
      have e2 : (∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          (if (L i b : ℕ) < L i a then 1 else 0) * (if (L k b : ℕ) < L i b then 1 else 0)) =
          ∑ b : Fin n, (∑ a : Fin n, if (L i b : ℕ) < L i a then 1 else 0) *
            (∑ k : Fin n, if (L k b : ℕ) < L i b then 1 else 0) := by
        rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul_sum]
        exact Finset.sum_comm
      rw [e2]
      simp_rw [hrowsum, fun b => hcolsum b _ (le_of_lt (L i b).isLt)]
      rw [← Fin.sum_univ_eq_sum_range (fun y => (n - 1 - y) * y) n]
      exact Equiv.sum_comp (Equiv.ofBijective _ (hrow i).bijective_of_finite)
        (fun y : Fin n => (n - 1 - (y : ℕ)) * y)
    rw [Finset.sum_congr rfl fun i _ => hrow' i]
    simp
  have hpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [Finset.sum_congr rfl fun μ _ => hB μ]
  calc n * (n - 1) * (6 * ∑ μ : Equiv.Perm (Fin n), ∑ i : Fin n, ∑ k : Fin n, G i k (μ i) (μ k))
      = 6 * (n * (n - 1) * ∑ μ : Equiv.Perm (Fin n), ∑ i : Fin n, ∑ k : Fin n,
          G i k (μ i) (μ k)) := by ring
    _ = n.factorial * n * (6 * ∑ y ∈ Finset.range n, (n - 1 - y) * y) := by
          rw [hstep, hT]; ring
    _ = n * (n - 1) * (n.factorial * (n * (n - 2))) := by rw [hf]; ring
