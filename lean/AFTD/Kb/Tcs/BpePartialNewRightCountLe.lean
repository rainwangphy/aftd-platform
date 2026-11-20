import AFTD.Prelude
import AFTD.Kb.Tcs.BpePartialMerge
import AFTD.Kb.Tcs.BpePairCount

/-!
# bpe_partial_new_right_count_le

Topic: algorithms   Node: b9308394608b

Provenance: helper lemma. Helper for arXiv:2611.08671v1, Lemma 17, and OP-1287: compare one pair count across a partial merge.

After a partial merge of a,b into a fresh symbol z, the nonoverlapping count of (x,z), for x different from z, is at most the original count of (x,a).
-/

theorem bpe_pnr_count_cons_bounds (a b : ℕ) :
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
          have ih := bpe_pnr_count_cons_bounds a b n u L' (by omega)
          rw [hc]
          constructor
          · omega
          · match L', hL' with
            | [], _ => simp [bpe_pair_count]
            | v :: L'', hL'' =>
              have ih2 := bpe_pnr_count_cons_bounds a b n v L'' (by simp at hL'' ⊢; omega)
              omega
        · have hc : bpe_pair_count a b (w :: u :: L') = bpe_pair_count a b (u :: L') := by
            simp [bpe_pair_count, hwu]
          rw [hc]; omega


theorem bpe_pnr_cons_le (a b w : ℕ) (L : List ℕ) : bpe_pair_count a b L ≤ bpe_pair_count a b (w :: L) :=
  (bpe_pnr_count_cons_bounds a b L.length w L le_rfl).1

theorem bpe_pnr_main (a b z x : ℕ) (hx : x ≠ z) :
    ∀ (n : ℕ) (s t : List ℕ), s.length ≤ n → z ∉ s → bpe_partial_merge a b z s t →
      bpe_pair_count x z t ≤ bpe_pair_count x a s
  | 0, s, t, hs, _, h => by
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hs)] at h ⊢
      simp [bpe_partial_merge] at h
      subst h; exact le_rfl
  | n+1, [], t, _, _, h => by simp [bpe_partial_merge] at h; subst h; simp [bpe_pair_count]
  | n+1, [x0], t, _, _, h => by simp [bpe_partial_merge] at h; subst h; simp [bpe_pair_count]
  | n+1, x0 :: y0 :: xs, t, hs, hz, h => by
      simp only [List.length_cons] at hs
      have hz0 : x0 ≠ z := fun e => hz (e ▸ List.mem_cons_self)
      have hzt : z ∉ y0 :: xs := fun e => hz (List.mem_cons_of_mem _ e)
      have hy0 : y0 ≠ z := fun e => hzt (e ▸ List.mem_cons_self)
      have hzxs : z ∉ xs := fun e => hzt (List.mem_cons_of_mem _ e)
      rcases h with ⟨out, rfl, hout⟩ | ⟨hxa, hyb, out, rfl, hout⟩
      · have ih := bpe_pnr_main a b z x hx n (y0 :: xs) out (by simp; omega) hzt hout
        match out, hout, ih with
        | [], _, _ => simp [bpe_pair_count]
        | o1 :: out', hout', ih' =>
          by_cases hxo : x0 = x ∧ o1 = z
          · have hc1 : bpe_pair_count x z (x0 :: o1 :: out') = 1 + bpe_pair_count x z out' := by
              simp [bpe_pair_count, hxo]
            match xs, hout', hs, hzxs with
            | [], hout'', _, _ =>
              simp [bpe_partial_merge] at hout''
              exact absurd (hout''.1 ▸ hxo.2) hy0
            | x1 :: xs', hout'', hs', hzxs' =>
              rcases hout'' with ⟨out2, hout2, -⟩ | ⟨hya, hxb, out2, hout2, hpm⟩
              · simp only [List.cons.injEq] at hout2
                exact absurd (hout2.1.symm.trans hxo.2) hy0
              · simp only [List.cons.injEq] at hout2
                obtain ⟨-, hoe⟩ := hout2
                have hzxs'' : z ∉ xs' := fun e => hzxs' (List.mem_cons_of_mem _ e)
                have ih2 := bpe_pnr_main a b z x hx n xs' out2 (by simp at hs' ⊢; omega) hzxs'' hpm
                have hc2 : bpe_pair_count x a (x0 :: y0 :: x1 :: xs') = 1 + bpe_pair_count x a (x1 :: xs') := by
                  simp [bpe_pair_count, hxo.1, hya]
                have hmono := bpe_pnr_cons_le x a x1 xs'
                rw [hc1, hc2, hoe]; omega
          · have hc1 : bpe_pair_count x z (x0 :: o1 :: out') = bpe_pair_count x z (o1 :: out') := by
              simp [bpe_pair_count, hxo]
            rw [hc1]
            exact le_trans ih' (bpe_pnr_cons_le x a x0 (y0 :: xs))
      · have ih := bpe_pnr_main a b z x hx n xs out (by omega) hzxs hout
        have hz' : bpe_pair_count x z (z :: out) ≤ bpe_pair_count x z out := by
          match out with
          | [] => simp [bpe_pair_count]
          | o :: out' =>
            have : ¬ (z = x ∧ o = z) := fun h => hx h.1.symm
            simp [bpe_pair_count, this]
        exact le_trans hz' (le_trans ih (le_trans (bpe_pnr_cons_le x a y0 xs) (bpe_pnr_cons_le x a x0 (y0 :: xs))))

theorem bpe_partial_new_right_count_le
    (a b z : ℕ) (s t : List ℕ) (hz : z ∉ s)
    (h : bpe_partial_merge a b z s t) (x : ℕ) (hx : x ≠ z) :
    bpe_pair_count x z t ≤ bpe_pair_count x a s := by
  exact bpe_pnr_main a b z x hx s.length s t le_rfl hz h
