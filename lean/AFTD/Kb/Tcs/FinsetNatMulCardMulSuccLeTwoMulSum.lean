import AFTD.Prelude

/-!
# finset_nat_mul_card_mul_succ_le_two_mul_sum

Topic: combinatorics   Node: 1feebaf55b74

Provenance: helper lemma. Step (2)–(3) of the proof of Lemma 1 in arXiv:2610.15860 (A note on the Slater–Vélez permutation): sums of sets with growing elements.

If S is a finite set of natural numbers in which every v is at least c times its rank (the number of elements of S that are ≤ v), then c·|S|(|S|+1) ≤ 2·Σ_{v∈S} v.
-/

theorem finset_nat_mul_card_mul_succ_le_two_mul_sum (c : ℕ) (S : Finset ℕ)
    (h : ∀ v ∈ S, c * (S.filter (· ≤ v)).card ≤ v) :
    c * (S.card * (S.card + 1)) ≤ 2 * ∑ v ∈ S, v := open Finset in by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert m S hlt ih =>
    have hm : m ∉ S := fun hm => lt_irrefl _ (hlt m hm)
    rw [card_insert_of_notMem hm, sum_insert hm]
    have h1 : c * (S.card + 1) ≤ m := by
      have := h m (mem_insert_self m S)
      have hf : (insert m S).filter (· ≤ m) = insert m S := by
        apply filter_true_of_mem
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact le_rfl
        · exact (hlt x hx).le
      rw [hf, card_insert_of_notMem hm] at this
      exact this
    have h2 : c * (S.card * (S.card + 1)) ≤ 2 * ∑ v ∈ S, v := by
      apply ih
      intro v hv
      have := h v (mem_insert_of_mem hv)
      have hf : (insert m S).filter (· ≤ v) = S.filter (· ≤ v) := by
        rw [filter_insert, if_neg (not_le.2 (hlt v hv))]
      rw [hf] at this
      exact this
    have e : c * ((S.card + 1) * (S.card + 1 + 1)) =
        c * (S.card * (S.card + 1)) + 2 * (c * (S.card + 1)) := by ring
    rw [e]
    omega
