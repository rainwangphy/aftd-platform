import AFTD.Prelude

/-!
# op1525_lower_incidence_descends

Topic: combinatorics   Node: b4a59423cae9

Provenance: helper lemma. Incidence-count helper for OP-1525 and arXiv:2611.13901, Remark 4.11.

If an integer function on finite subsets is supported on k-element sets and its sum over supersets is zero at every (k−1)-element set, then the same sum vanishes at every set of cardinality less than k.
-/

theorem op1525_lower_incidence_descends {V : Type} [DecidableEq V] [Fintype V]
    (f : Finset V → ℤ) (k : ℕ)
    (hsupport : ∀ T, f T ≠ 0 → T.card = k)
    (htop : ∀ R : Finset V, R.card + 1 = k →
      (∑ T ∈ (Finset.univ : Finset V).powerset, if R ⊆ T then f T else 0) = 0) :
    ∀ R : Finset V, R.card < k →
      (∑ T ∈ (Finset.univ : Finset V).powerset, if R ⊆ T then f T else 0) = 0 := by
  classical
  let H : Finset V → ℤ := fun R =>
    ∑ T ∈ (Finset.univ : Finset V).powerset, if R ⊆ T then f T else 0
  have hstep (R : Finset V) (hlt : R.card < k)
      (hnext : ∀ x, x ∉ R → H (insert x R) = 0) : H R = 0 := by
    have hz : (∑ x ∈ (Finset.univ \ R), H (insert x R)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      apply hnext x
      simpa using hx
    have hcount (T : Finset V) :
        (∑ x ∈ (Finset.univ \ R), if insert x R ⊆ T then f T else 0) =
          if R ⊆ T then ((k - R.card : ℕ) : ℤ) * f T else 0 := by
      by_cases hRT : R ⊆ T
      · by_cases hf : f T = 0
        · simp [hf]
        · have hcard := hsupport T hf
          have heq : (Finset.univ \ R).filter (fun x => x ∈ T) = T \ R := by
            ext x
            simp
            tauto
          simp only [Finset.insert_subset_iff, hRT, and_true, if_true]
          rw [← Finset.sum_filter, heq, Finset.sum_const,
            Finset.card_sdiff_of_subset hRT, hcard]
          simp
      · have hnone : ∀ x, ¬ insert x R ⊆ T := by
          intro x h
          exact hRT (fun y hy => h (Finset.mem_insert_of_mem hy))
        simp [hRT, hnone]
    have hidentity : (∑ x ∈ (Finset.univ \ R), H (insert x R)) =
        ((k - R.card : ℕ) : ℤ) * H R := by
      dsimp [H]
      rw [Finset.sum_comm]
      simp_rw [hcount]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      split_ifs <;> simp
    rw [hidentity] at hz
    have hn : ((k - R.card : ℕ) : ℤ) ≠ 0 := by
      have hnNat : k - R.card ≠ 0 := by omega
      exact_mod_cast hnNat
    exact (mul_eq_zero.mp hz).resolve_left hn
  have hall : ∀ d : ℕ, ∀ R : Finset V, R.card < k → k - R.card = d → H R = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro R hlt hd
      by_cases heq : R.card + 1 = k
      · exact htop R heq
      · apply hstep R hlt
        intro x hx
        have hc : (insert x R).card = R.card + 1 := Finset.card_insert_of_notMem hx
        have hlt' : (insert x R).card < k := by omega
        apply ih (k - (insert x R).card) (by omega) (insert x R) hlt' rfl
  intro R hR
  exact hall (k - R.card) R hR rfl
