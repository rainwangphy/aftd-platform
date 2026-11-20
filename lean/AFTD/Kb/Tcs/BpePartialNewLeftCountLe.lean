import AFTD.Prelude
import AFTD.Kb.Tcs.BpePartialMerge
import AFTD.Kb.Tcs.BpePairCount

/-!
# bpe_partial_new_left_count_le

Topic: algorithms   Node: 8f4af5d6c9bb

Provenance: helper lemma. Helper for arXiv:2611.08671v1, Lemma 17, and OP-1287: compare one pair count across a partial merge.

After a partial merge of a,b into a fresh symbol z, the nonoverlapping count of (z,y), for y different from z, is at most the original count of (b,y).
-/

theorem bpe_pnl_count_cons_bounds (a b : ℕ) :
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
          have ih := bpe_pnl_count_cons_bounds a b n u L' (by omega)
          rw [hc]
          constructor
          · omega
          · match L', hL' with
            | [], _ => simp [bpe_pair_count]
            | v :: L'', hL'' =>
              have ih2 := bpe_pnl_count_cons_bounds a b n v L'' (by simp at hL'' ⊢; omega)
              omega
        · have hc : bpe_pair_count a b (w :: u :: L') = bpe_pair_count a b (u :: L') := by
            simp [bpe_pair_count, hwu]
          rw [hc]; omega


theorem bpe_pnl_cons_le (a b w : ℕ) (L : List ℕ) : bpe_pair_count a b L ≤ bpe_pair_count a b (w :: L) :=
  (bpe_pnl_count_cons_bounds a b L.length w L le_rfl).1

theorem bpe_pnl_main (a b z y : ℕ) (hy : y ≠ z) :
    ∀ (n : ℕ) (s t : List ℕ), s.length ≤ n → z ∉ s → bpe_partial_merge a b z s t →
      bpe_pair_count z y t ≤ bpe_pair_count b y s
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
      have hzxs : z ∉ xs := fun e => hzt (List.mem_cons_of_mem _ e)
      rcases h with ⟨out, rfl, hout⟩ | ⟨hxa, hyb, out, rfl, hout⟩
      · have ih := bpe_pnl_main a b z y hy n (y0 :: xs) out (by simp; omega) hzt hout
        match out, hout, ih with
        | [], _, _ => simp [bpe_pair_count]
        | o1 :: out', hout', ih' =>
          have hxo : ¬ (x0 = z ∧ o1 = y) := fun h => hz0 h.1
          have hc1 : bpe_pair_count z y (x0 :: o1 :: out') = bpe_pair_count z y (o1 :: out') := by
            simp [bpe_pair_count, hxo]
          rw [hc1]
          exact le_trans ih' (bpe_pnl_cons_le b y x0 (y0 :: xs))
      · subst y0
        match out, hout with
        | [], _ => simp [bpe_pair_count]
        | o :: out', hout' =>
          by_cases hoy : o = y
          · subst hoy
            have hc1 : bpe_pair_count z o (z :: o :: out') = 1 + bpe_pair_count z o out' := by
              simp [bpe_pair_count]
            match xs, hout', hs, hzxs with
            | [], hout'', _, _ => simp [bpe_partial_merge] at hout''
            | [x1], hout'', _, _ =>
              simp [bpe_partial_merge] at hout''
              obtain ⟨rfl, rfl⟩ := hout''
              rw [hc1]
              have : bpe_pair_count b o (x0 :: b :: [o]) ≥ 1 := by
                by_cases hh : x0 = b ∧ b = o
                · simp [bpe_pair_count, hh]
                · simp [bpe_pair_count, hh]
              have h0 : bpe_pair_count z o [] = 0 := by simp [bpe_pair_count]
              rw [h0]
              exact this
            | x1 :: x2 :: xs', hout'', hs', hzxs' =>
              rcases hout'' with ⟨out2, hout2, hpm⟩ | ⟨-, -, out2, hout2, -⟩
              · simp only [List.cons.injEq] at hout2
                obtain ⟨hox, hoe⟩ := hout2
                have hzxs'' : z ∉ x2 :: xs' := fun e => hzxs' (List.mem_cons_of_mem _ e)
                have ih2 := bpe_pnl_main a b z o hy n (x2 :: xs') out2 (by simp at hs' ⊢; omega) hzxs'' hpm
                have hlow : 1 + bpe_pair_count b o (x2 :: xs') ≤ bpe_pair_count b o (x0 :: b :: x1 :: x2 :: xs') := by
                  rw [← hox]
                  by_cases hh : x0 = b ∧ b = o
                  · have h3 : bpe_pair_count b o (x0 :: b :: o :: x2 :: xs') = 1 + bpe_pair_count b o (o :: x2 :: xs') := by
                      simp [bpe_pair_count, hh]
                    rw [h3]
                    have := bpe_pnl_cons_le b o o (x2 :: xs')
                    omega
                  · have h3 : bpe_pair_count b o (x0 :: b :: o :: x2 :: xs') = bpe_pair_count b o (b :: o :: x2 :: xs') := by
                      simp [bpe_pair_count, hh]
                    rw [h3]
                    simp [bpe_pair_count]
                rw [hc1, hoe]; omega
              · simp only [List.cons.injEq] at hout2
                exact absurd hout2.1 hy
          · have hc1 : bpe_pair_count z y (z :: o :: out') = bpe_pair_count z y (o :: out') := by
              simp [bpe_pair_count, hoy]
            have ih := bpe_pnl_main a b z y hy n xs (o :: out') (by omega) hzxs hout'
            rw [hc1]
            exact le_trans ih (le_trans (bpe_pnl_cons_le b y b xs) (bpe_pnl_cons_le b y x0 (b :: xs)))

theorem bpe_partial_new_left_count_le
    (a b z : ℕ) (s t : List ℕ) (hz : z ∉ s)
    (h : bpe_partial_merge a b z s t) (y : ℕ) (hy : y ≠ z) :
    bpe_pair_count z y t ≤ bpe_pair_count b y s := by
  exact bpe_pnl_main a b z y hy s.length s t le_rfl hz h
