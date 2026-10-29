import AFTD.Prelude
import AFTD.Kb.Tcs.SubsequenceSums
import AFTD.Kb.Tcs.IsMaximalZeroSumFree
import AFTD.Kb.Tcs.MemSubsequenceSums

/-!
# is_maximal_zero_sum_free_subsequence_sums_pred_eq_univ

Topic: combinatorics   Node: 6c336fd278d2

Provenance: formalization of a published result. Source: arXiv:2610.35819 Section 8

Let G be a finite additive commutative group with decidable equality, let n ≥ 1 be a natural number, and let S be a multiset over G satisfying is_maximal_zero_sum_free n S. Then the finite set of (n - 1)-term subsequence sums of S, subsequence_sums (n - 1) S, equals the universal set Finset.univ of G.
-/

/-- A maximal sequence without n-term zero-sums covers all elements as (n-1)-term subsequence sums. -/
theorem is_maximal_zero_sum_free_subsequence_sums_pred_eq_univ
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {n : ℕ} (hn : 1 ≤ n)
    (S : Multiset G) (hS : is_maximal_zero_sum_free n S) :
    subsequence_sums (n - 1) S = (Finset.univ : Finset G) := by
  obtain ⟨hno, hmax⟩ := hS
  apply Finset.eq_univ_of_forall
  intro g
  rw [mem_subsequence_sums]
  obtain ⟨W, hWle, hWcard, hWsum⟩ := hmax (-g)
  have hxmem : -g ∈ W := by
    by_contra hx
    apply hno
    refine ⟨W, ?_, hWcard, hWsum⟩
    rw [Multiset.le_iff_count]
    intro a
    have h := (Multiset.le_iff_count.mp hWle) a
    rw [Multiset.count_add, Multiset.count_singleton] at h
    by_cases ha : a = -g
    · subst ha
      rw [if_pos rfl, Nat.add_zero] at h
      rw [Multiset.count_eq_zero.mpr hx]
      exact Nat.zero_le _
    · rw [if_neg ha] at h
      simpa using h
  refine ⟨W.erase (-g), ?_, ?_, ?_⟩
  · have h := Multiset.erase_le_erase (-g) hWle
    have h1 : (S + {-g}).erase (-g) = S := by
      ext a
      by_cases h' : a = -g
      · subst h'
        simp [Multiset.count_erase_self, Multiset.count_add]
      · simp [Multiset.count_erase_of_ne, h', Multiset.count_add]
    rwa [h1] at h
  · rw [Multiset.card_erase_of_mem hxmem, hWcard]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp
  · have h := Multiset.sum_erase hxmem
    rw [hWsum] at h
    have h2 : (W.erase (-g)).sum + (-g) = 0 := by rw [add_comm]; exact h
    have : (W.erase (-g)).sum = -(-g) := eq_neg_of_add_eq_zero_left h2
    simpa using this
