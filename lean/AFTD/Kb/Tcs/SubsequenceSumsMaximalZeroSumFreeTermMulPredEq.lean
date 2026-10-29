import AFTD.Prelude
import AFTD.Kb.Tcs.SubsequenceSums
import AFTD.Kb.Tcs.IsMaximalZeroSumFree
import AFTD.Kb.Tcs.IsMaximalZeroSumFreeSubsequenceSumsPredEqUniv
import AFTD.Kb.Tcs.MemSubsequenceSums

/-!
# subsequence_sums_maximal_zero_sum_free_term_mul_pred_eq

Topic: combinatorics   Node: c01b43f80985

Provenance: formalization of a published result. Source: arXiv:2610.35819 Proposition 8.2

Let G be a finite additive commutative group with decidable equality and exponent n (AddMonoid.exponent G = n). Let S be a multiset over G satisfying is_maximal_zero_sum_free n S. If some element t of G has multiplicity n - 1 in S (S.count t = n - 1), then the finite set of n-term subsequence sums of S equals the nonzero elements of G: subsequence_sums n S = (Finset.univ : Finset G) \ {0}.
-/

/-- If S is maximal without n-term zero-sums and has a term of multiplicity n - 1, its n-term sums cover all nonzero elements. -/
theorem subsequence_sums_maximal_zero_sum_free_term_mul_pred_eq
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {n : ℕ}
    (hn : AddMonoid.exponent G = n)
    (S : Multiset G) (hS : is_maximal_zero_sum_free n S)
    {t : G} (ht : S.count t = n - 1) :
    subsequence_sums n S = (Finset.univ : Finset G) \ {0} := by
  have hn1 : 1 ≤ n := by
    have h : 0 < AddMonoid.exponent G :=
      AddMonoid.exponent_pos.mpr AddMonoid.ExponentExists.of_finite
    omega
  have hnsmul : n • t = 0 := by
    rw [← hn]
    exact AddMonoid.exponent_nsmul_eq_zero t
  have hpred : (n - 1) • t = -t := by
    have h : n • t = (n - 1) • t + t := by
      conv_lhs => rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn1).symm]
      rw [add_nsmul, one_nsmul]
    have h2 : (n - 1) • t + t = 0 := by rw [← h]; exact hnsmul
    exact eq_neg_of_add_eq_zero_left h2
  have hmemuniv : ∀ x : G, ∃ U ≤ S, U.card = n - 1 ∧ U.sum = x := by
    intro x
    have h : x ∈ subsequence_sums (n - 1) S := by
      rw [is_maximal_zero_sum_free_subsequence_sums_pred_eq_univ hn1 S hS]
      exact Finset.mem_univ x
    exact (mem_subsequence_sums S x).mp h
  ext g
  simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, true_and,
    mem_subsequence_sums]
  constructor
  · rintro ⟨U, hUle, hUcard, hUsum⟩ hg0
    apply hS.1
    exact ⟨U, hUle, hUcard, by rw [hUsum, hg0]⟩
  · intro hg0
    obtain ⟨U, hUle, hUcard, hUsum⟩ := hmemuniv (g - t)
    have hUcount_le : U.count t ≤ n - 1 := by
      have h := (Multiset.le_iff_count.mp hUle) t
      rwa [ht] at h
    by_cases hc : U.count t = n - 1
    · exfalso
      apply hg0
      have hcardf : (U.filter (fun x => x = t)).card = U.card := by
        rw [Multiset.filter_eq' U t, Multiset.card_replicate, hc, hUcard]
      have heq : U.filter (fun x => x = t) = U :=
        Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _) (le_of_eq hcardf.symm)
      have hUeq : U = Multiset.replicate (n - 1) t := by
        rw [← heq, Multiset.filter_eq' U t, hc]
      have hgt : g - t = -t := by
        rw [← hUsum, hUeq, Multiset.sum_replicate, hpred]
      have hg : g = 0 := by
        have := congrArg (· + t) hgt
        simpa using this
      exact hg
    · have hlt : U.count t ≤ n - 2 := by omega
      refine ⟨U + {t}, ?_, ?_, ?_⟩
      · rw [Multiset.le_iff_count]
        intro a
        rw [Multiset.count_add, Multiset.count_singleton]
        by_cases ha : a = t
        · subst ha
          rw [if_pos rfl, ht]
          omega
        · rw [if_neg ha]
          have h := (Multiset.le_iff_count.mp hUle) a
          simpa using h
      · rw [Multiset.card_add, Multiset.card_singleton, hUcard]
        omega
      · rw [Multiset.sum_add, Multiset.sum_singleton, hUsum, sub_add_cancel]
