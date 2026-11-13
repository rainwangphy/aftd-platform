import AFTD.Prelude

/-!
# op1525_complement_sum_parity

Topic: combinatorics   Node: d936e1aac24a

Provenance: helper lemma. Inclusion-exclusion helper for the subset-deletion route to OP-1525, arXiv:2611.13901, Remark 4.11.

Let f assign integers to subsets of a finite set, with f supported on subsets of size k. If every sum of f over the supersets of each subset of size less than k vanishes, then for every S the sum of f over subsets of the complement of S equals (-1)^k times the sum over subsets of S.
-/

theorem op1525_complement_sum_parity
    {V : Type} [DecidableEq V] [Fintype V] (f : Finset V → ℤ) (k : ℕ)
    (hsupport : ∀ T, f T ≠ 0 → T.card = k)
    (hlower : ∀ R : Finset V, R.card < k →
      (∑ T ∈ (Finset.univ : Finset V).powerset, if R ⊆ T then f T else 0) = 0)
    (S : Finset V) :
    (∑ T ∈ (Finset.univ \ S).powerset, f T) =
      (-1 : ℤ)^k * (∑ T ∈ S.powerset, f T) := by
  classical
  have hcancel (T : Finset V) :
      (∑ R ∈ S.powerset, if R ⊆ T then (-1 : ℤ)^R.card else 0) =
        if Disjoint S T then 1 else 0 := by
    rw [← Finset.sum_filter]
    have heq : S.powerset.filter (fun R => R ⊆ T) = (S ∩ T).powerset := by
      ext R
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
    rw [heq, Finset.sum_powerset_neg_one_pow_card]
    simp [Finset.disjoint_iff_inter_eq_empty]
  have htop (R : Finset V) (hR : R.card = k) :
      (∑ T ∈ (Finset.univ : Finset V).powerset, if R ⊆ T then f T else 0) = f R := by
    have hsum := Finset.sum_eq_single R (s := (Finset.univ : Finset V).powerset)
      (f := fun T => if R ⊆ T then f T else 0)
    have hresult : (∑ T ∈ (Finset.univ : Finset V).powerset, if R ⊆ T then f T else 0) =
        (if R ⊆ R then f R else 0) := by
      apply hsum
      · intro T _ hne
        by_cases hRT : R ⊆ T
        · have hft : f T = 0 := by
            by_contra hn
            have hc := hsupport T hn
            have he : R = T := Finset.eq_of_subset_of_card_le hRT (by omega)
            exact hne he.symm
          simp [hft]
        · simp [hRT]
      · simp
    simpa using hresult
  have hlarge (R : Finset V) (hR : k < R.card) :
      (∑ T ∈ (Finset.univ : Finset V).powerset, if R ⊆ T then f T else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro T _
    by_cases hRT : R ⊆ T
    · have hf : f T = 0 := by
        by_contra hn
        have hc := hsupport T hn
        have hle := Finset.card_le_card hRT
        omega
      simp [hf]
    · simp [hRT]
  calc
    (∑ T ∈ (Finset.univ \ S).powerset, f T) =
        ∑ T ∈ (Finset.univ : Finset V).powerset,
          f T * (∑ R ∈ S.powerset, if R ⊆ T then (-1 : ℤ)^R.card else 0) := by
      simp_rw [hcancel]
      simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
      simp [Finset.subset_sdiff, Finset.disjoint_left]
      aesop
    _ = ∑ R ∈ S.powerset, (-1 : ℤ)^R.card *
        (∑ T ∈ (Finset.univ : Finset V).powerset, if R ⊆ T then f T else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro R _
      apply Finset.sum_congr rfl
      intro T _
      split_ifs <;> simp [mul_comm]
    _ = ∑ R ∈ S.powerset, (-1 : ℤ)^k * f R := by
      apply Finset.sum_congr rfl
      intro R _
      rcases lt_trichotomy R.card k with h | h | h
      · have hf : f R = 0 := by
          by_contra hn
          have hc := hsupport R hn
          omega
        rw [hlower R h, hf]
        simp
      · rw [htop R h, h]
      · have hf : f R = 0 := by
          by_contra hn
          have hc := hsupport R hn
          omega
        rw [hlarge R h, hf]
        simp
    _ = (-1 : ℤ)^k * (∑ T ∈ S.powerset, f T) := by rw [Finset.mul_sum]
