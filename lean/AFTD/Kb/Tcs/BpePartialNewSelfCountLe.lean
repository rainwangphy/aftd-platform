import AFTD.Prelude
import AFTD.Kb.Tcs.BpePartialMerge
import AFTD.Kb.Tcs.BpePairCount

/-!
# bpe_partial_new_self_count_le

Topic: algorithms   Node: c8c8f5a53b51

Provenance: helper lemma. Helper for arXiv:2611.08671v1, Lemma 17, and OP-1287: compare one pair count across a partial merge.

After a partial merge of a,b into a fresh symbol z, the nonoverlapping count of (z,z) is at most the original count of (b,a).
-/

theorem bpe_pns_count_cons_bounds (a b : ℕ) :
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
          have ih := bpe_pns_count_cons_bounds a b n u L' (by omega)
          rw [hc]
          constructor
          · omega
          · match L', hL' with
            | [], _ => simp [bpe_pair_count]
            | v :: L'', hL'' =>
              have ih2 := bpe_pns_count_cons_bounds a b n v L'' (by simp at hL'' ⊢; omega)
              omega
        · have hc : bpe_pair_count a b (w :: u :: L') = bpe_pair_count a b (u :: L') := by
            simp [bpe_pair_count, hwu]
          rw [hc]; omega


theorem bpe_pns_cons_le (a b w : ℕ) (L : List ℕ) : bpe_pair_count a b L ≤ bpe_pair_count a b (w :: L) :=
  (bpe_pns_count_cons_bounds a b L.length w L le_rfl).1

theorem bpe_pns_main (a b z : ℕ) :
    ∀ (n : ℕ) (s t : List ℕ), s.length ≤ n → z ∉ s → bpe_partial_merge a b z s t →
      bpe_pair_count z z t ≤ bpe_pair_count b a s
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
      · have ih := bpe_pns_main a b z n (y0 :: xs) out (by simp; omega) hzt hout
        match out, hout, ih with
        | [], _, _ => simp [bpe_pair_count]
        | o1 :: out', hout', ih' =>
          have hxo : ¬ (x0 = z ∧ o1 = z) := fun h => hz0 h.1
          have hc1 : bpe_pair_count z z (x0 :: o1 :: out') = bpe_pair_count z z (o1 :: out') := by
            simp [bpe_pair_count, hxo]
          rw [hc1]
          exact le_trans ih' (bpe_pns_cons_le b a x0 (y0 :: xs))
      · subst x0 y0
        match out, hout with
        | [], _ => simp [bpe_pair_count]
        | o :: out', hout' =>
          by_cases hoz : o = z
          · subst o
            have hc1 : bpe_pair_count z z (z :: z :: out') = 1 + bpe_pair_count z z out' := by
              simp [bpe_pair_count]
            match xs, hout', hs, hzxs with
            | [], hout'', _, _ => simp [bpe_partial_merge] at hout''
            | [x1], hout'', _, hzxs' =>
              simp [bpe_partial_merge] at hout''
              exact absurd (hout''.1 ▸ List.mem_cons_self) hzxs'
            | x1 :: x2 :: xs', hout'', hs', hzxs' =>
              rcases hout'' with ⟨out2, hout2, -⟩ | ⟨hx1, hx2, out2, hout2, hpm⟩
              · simp only [List.cons.injEq] at hout2
                exact absurd (hout2.1 ▸ List.mem_cons_self) hzxs'
              · simp only [List.cons.injEq] at hout2
                obtain ⟨-, hoe⟩ := hout2
                have hzxs'' : z ∉ xs' := by
                  intro e; exact hzxs' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ e))
                have ih2 := bpe_pns_main a b z n xs' out2 (by simp at hs' ⊢; omega) hzxs'' hpm
                subst x1 x2
                have hlow : 1 + bpe_pair_count b a xs' ≤ bpe_pair_count b a (a :: b :: a :: b :: xs') := by
                  by_cases hab : a = b
                  · subst hab
                    have h3 : bpe_pair_count a a (a :: a :: a :: a :: xs') = 1 + bpe_pair_count a a (a :: a :: xs') := by
                      simp [bpe_pair_count]
                    rw [h3]
                    have := bpe_pns_cons_le a a a xs'
                    have := bpe_pns_cons_le a a a (a :: xs')
                    omega
                  · have hh : ¬ (a = b ∧ b = a) := fun h => hab h.1
                    have h3 : bpe_pair_count b a (a :: b :: a :: b :: xs') = 1 + bpe_pair_count b a (b :: xs') := by
                      simp [bpe_pair_count, hh]
                    rw [h3]
                    have := bpe_pns_cons_le b a b xs'
                    omega
                rw [hc1, hoe]; omega
          · have hc1 : bpe_pair_count z z (z :: o :: out') = bpe_pair_count z z (o :: out') := by
              simp [bpe_pair_count, hoz]
            have ih := bpe_pns_main a b z n xs (o :: out') (by omega) hzxs hout'
            rw [hc1]
            exact le_trans ih (le_trans (bpe_pns_cons_le b a b xs) (bpe_pns_cons_le b a a (b :: xs)))

theorem bpe_partial_new_self_count_le
    (a b z : ℕ) (s t : List ℕ) (hz : z ∉ s)
    (h : bpe_partial_merge a b z s t)  :
    bpe_pair_count z z t ≤ bpe_pair_count b a s := by
  exact bpe_pns_main a b z s.length s t le_rfl hz h
