import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetUnorderedSumRepCount

/-!
# finset_has_no_unique_sums_univ_zmod

Topic: combinatorics   Node: b11adda81a02

Provenance: formalization of a published result. Source: arXiv:2610.09349 (A near-quadratic lower bound for sets with no unique sums), Sec. 1 (F_p itself is NUS: each s has (p+1)/2 ≥ 2 unordered representations).

For an odd prime p, the whole of Z/pZ has no unique sums.
-/

theorem finset_has_no_unique_sums_univ_zmod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    finset_has_no_unique_sums (Finset.univ : Finset (ZMod p)) := by
  constructor
  · rw [Finset.card_univ, ZMod.card p]
    have : 2 < p := Nat.lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)
    exact le_of_lt this
  · intros a _ b _
    unfold finset_unordered_sum_rep_count
    set s : ZMod p := a + b
    by_cases hs : s = 1
    · rw [Nat.add_one_le_iff]
      apply Finset.one_lt_card.2
      refine ⟨s(0, 1), ?_, s(2, -1), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨by simp, ?_⟩
        show (0 : ZMod p) + 1 = s
        rw [hs, zero_add]
      · rw [Finset.mem_filter]
        refine ⟨by simp, ?_⟩
        show (2 : ZMod p) + (-1) = s
        rw [hs]
        ring
      · intro h
        rw [Sym2.eq_iff] at h
        rcases h with ⟨h02, -⟩ | ⟨h0neg, -⟩
        · have hp2 : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h02.symm
          have hle := Nat.le_of_dvd (by decide) hp2
          have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
          exact hp (Nat.le_antisymm hle hge)
        · have : (1 : ZMod p) = 0 := by
            calc (1 : ZMod p) = - (-1) := by ring
            _ = - 0 := by rw [← h0neg]
            _ = 0 := by ring
          exact one_ne_zero this
    · rw [Nat.add_one_le_iff]
      apply Finset.one_lt_card.2
      refine ⟨s(0, s), ?_, s(1, s - 1), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨by simp, ?_⟩
        show (0 : ZMod p) + s = s
        exact zero_add s
      · rw [Finset.mem_filter]
        refine ⟨by simp, ?_⟩
        show (1 : ZMod p) + (s - 1) = s
        ring
      · intro h
        rw [Sym2.eq_iff] at h
        rcases h with ⟨h01, -⟩ | ⟨-, hs1⟩
        · exact one_ne_zero h01.symm
        · exact hs hs1
