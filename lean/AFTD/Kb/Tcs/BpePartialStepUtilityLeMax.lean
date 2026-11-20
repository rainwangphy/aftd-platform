import AFTD.Prelude
import AFTD.Kb.Tcs.BpePartialStep
import AFTD.Kb.Tcs.BpePartialMerge
import AFTD.Kb.Tcs.BpePairCount
import AFTD.Kb.Tcs.BpeMaxPairCount

/-!
# bpe_partial_step_utility_le_max

Topic: algorithms   Node: 44554ca4f023

Provenance: helper lemma. Helper for the i = 0 case of OP-1287; arXiv:2611.08671v1, Lemma 17.

The decrease in string length caused by one partial merge step is at most the largest nonoverlapping pair count in the input string.
-/

theorem bpe_psu_count_cons_bounds (a b : ℕ) :
    ∀ (n : ℕ) (w : ℕ) (L : List ℕ), L.length ≤ n →
      bpe_pair_count a b L ≤ bpe_pair_count a b (w :: L) ∧
      bpe_pair_count a b (w :: L) ≤ bpe_pair_count a b L + 1
  | 0, w, L, hL => by
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hL)]
      simp [bpe_pair_count]
  | n+1, w, L, hL => by
      match L, hL with
      | [], _ => simp [bpe_pair_count]
      | u :: L', hL' =>
        simp only [List.length_cons] at hL'
        by_cases hwu : w = a ∧ u = b
        · have hc : bpe_pair_count a b (w :: u :: L') = 1 + bpe_pair_count a b L' := by
            simp [bpe_pair_count, hwu]
          have ih := bpe_psu_count_cons_bounds a b n u L' (by omega)
          rw [hc]
          constructor
          · omega
          · match L', hL' with
            | [], _ => simp [bpe_pair_count]
            | v :: L'', hL'' =>
              have ih2 := bpe_psu_count_cons_bounds a b n v L'' (by simp at hL'' ⊢; omega)
              omega
        · have hc : bpe_pair_count a b (w :: u :: L') = bpe_pair_count a b (u :: L') := by
            simp [bpe_pair_count, hwu]
          rw [hc]; omega

theorem bpe_psu_merge_bound (a b z : ℕ) :
    ∀ (s t : List ℕ), bpe_partial_merge a b z s t →
      t.length ≤ s.length ∧ s.length - t.length ≤ bpe_pair_count a b s
  | [], t, h => by simp [bpe_partial_merge] at h; subst h; simp
  | [x], t, h => by simp [bpe_partial_merge] at h; subst h; simp
  | x :: y :: xs, t, h => by
      rcases h with ⟨out, rfl, hout⟩ | ⟨hxa, hyb, out, rfl, hout⟩
      · obtain ⟨h1, h2⟩ := bpe_psu_merge_bound a b z (y :: xs) out hout
        have hb := (bpe_psu_count_cons_bounds a b (y :: xs).length x (y :: xs) le_rfl).1
        simp only [List.length_cons] at h1 h2 ⊢
        omega
      · obtain ⟨h1, h2⟩ := bpe_psu_merge_bound a b z xs out hout
        have hc : bpe_pair_count a b (x :: y :: xs) = 1 + bpe_pair_count a b xs := by
          simp [bpe_pair_count, hxa, hyb]
        rw [hc]
        simp only [List.length_cons] at h1 h2 ⊢
        omega

theorem bpe_psu_pos_mem_zip (a b : ℕ) (s : List ℕ) (h : 0 < bpe_pair_count a b s) :
    (a, b) ∈ s.zip s.tail := by
  refine bpe_pair_count.induct a b (fun s => 0 < bpe_pair_count a b s → (a, b) ∈ s.zip s.tail) ?_ ?_ ?_ ?_ s h
  · simp [bpe_pair_count]
  · intro x
    simp [bpe_pair_count]
  · intro x y xs hxy _ _
    simp [hxy]
  · intro x y xs hxy ih hpos
    have hc : bpe_pair_count a b (x :: y :: xs) = bpe_pair_count a b (y :: xs) := by
      simp [bpe_pair_count, hxy]
    rw [hc] at hpos
    have hmem := ih hpos
    simp only [List.zip_cons_cons, List.tail_cons]
    exact List.mem_cons_of_mem _ hmem

theorem bpe_psu_count_le_max (a b : ℕ) (s : List ℕ) : bpe_pair_count a b s ≤ bpe_max_pair_count s := by
  rcases Nat.eq_zero_or_pos (bpe_pair_count a b s) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have hmem := bpe_psu_pos_mem_zip a b s hpos
    have hle := Finset.le_sup (s := (s.zip s.tail).toFinset)
      (f := fun p : ℕ × ℕ => bpe_pair_count p.1 p.2 s) (by simpa using hmem)
    simpa [bpe_max_pair_count] using hle

theorem bpe_partial_step_utility_le_max
    (s t : List ℕ) (h : bpe_partial_step s t) :
    s.length - t.length ≤ bpe_max_pair_count s := by
  rcases h with rfl | ⟨a, b, z, -, hm⟩
  · simp
  · exact le_trans (bpe_psu_merge_bound a b z s t hm).2 (bpe_psu_count_le_max a b s)
