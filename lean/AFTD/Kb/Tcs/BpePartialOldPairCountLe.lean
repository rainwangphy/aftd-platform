import AFTD.Prelude
import AFTD.Kb.Tcs.BpePartialMerge
import AFTD.Kb.Tcs.BpePairCount

/-!
# bpe_partial_old_pair_count_le

Topic: algorithms   Node: 3746f0a61de0

Provenance: helper lemma. Helper for arXiv:2611.08671v1, Lemma 17, and OP-1287: compare one pair count across a partial merge.

If neither queried symbol is the fresh output symbol, the nonoverlapping count of that ordered pair cannot increase under a partial merge.
-/

theorem bpe_pocl_count_cons_bounds (a b : ℕ) :
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
          have ih := bpe_pocl_count_cons_bounds a b n u L' (by omega)
          rw [hc]
          constructor
          · omega
          · match L', hL' with
            | [], _ => simp [bpe_pair_count]
            | v :: L'', hL'' =>
              have ih2 := bpe_pocl_count_cons_bounds a b n v L'' (by simp at hL'' ⊢; omega)
              omega
        · have hc : bpe_pair_count a b (w :: u :: L') = bpe_pair_count a b (u :: L') := by
            simp [bpe_pair_count, hwu]
          rw [hc]; omega


theorem bpe_pocl_cons_le (a b w : ℕ) (L : List ℕ) : bpe_pair_count a b L ≤ bpe_pair_count a b (w :: L) :=
  (bpe_pocl_count_cons_bounds a b L.length w L le_rfl).1

theorem bpe_pocl_main (a b z x y : ℕ) (hx : x ≠ z) (hy : y ≠ z) :
    ∀ (n : ℕ) (s t : List ℕ), s.length ≤ n → bpe_partial_merge a b z s t →
      bpe_pair_count x y t ≤ bpe_pair_count x y s
  | 0, s, t, hs, h => by
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hs)] at h ⊢
      simp [bpe_partial_merge] at h
      subst h; exact le_rfl
  | n+1, [], t, _, h => by simp [bpe_partial_merge] at h; subst h; exact le_rfl
  | n+1, [x0], t, _, h => by simp [bpe_partial_merge] at h; subst h; exact le_rfl
  | n+1, x0 :: y0 :: xs, t, hs, h => by
      simp only [List.length_cons] at hs
      rcases h with ⟨out, rfl, hout⟩ | ⟨hxa, hyb, out, rfl, hout⟩
      · -- keep x0
        have ih := bpe_pocl_main a b z x y hx hy n (y0 :: xs) out (by simp; omega) hout
        match out, hout, ih with
        | [], _, _ => simp [bpe_pair_count]
        | o1 :: out', hout', ih' =>
          by_cases hxo : x0 = x ∧ o1 = y
          · -- o1 is an old symbol, so it is y0 and the rest is a merge of xs
            have hc1 : bpe_pair_count x y (x0 :: o1 :: out') = 1 + bpe_pair_count x y out' := by
              simp [bpe_pair_count, hxo]
            match xs, hout', hs with
            | [], hout'', _ =>
              simp [bpe_partial_merge] at hout''
              obtain ⟨rfl, rfl⟩ := hout''
              simp [bpe_pair_count, hxo]
            | x1 :: xs', hout'', hs' =>
              rcases hout'' with ⟨out2, hout2, hpm⟩ | ⟨-, -, out2, hout2, hpm⟩
              · simp only [List.cons.injEq] at hout2
                obtain ⟨ho1, hoe⟩ := hout2
                have hy0 : y0 = y := ho1.symm.trans hxo.2
                have hc2 : bpe_pair_count x y (x0 :: y0 :: x1 :: xs') = 1 + bpe_pair_count x y (x1 :: xs') := by
                  simp [bpe_pair_count, hxo.1, hy0]
                have ih2 := bpe_pocl_main a b z x y hx hy n (x1 :: xs') out2 (by simp at hs' ⊢; omega) hpm
                rw [hc1, hc2, hoe]; omega
              · simp only [List.cons.injEq] at hout2
                exact absurd (hxo.2.symm.trans hout2.1) hy
          · have hc1 : bpe_pair_count x y (x0 :: o1 :: out') = bpe_pair_count x y (o1 :: out') := by
              simp [bpe_pair_count, hxo]
            rw [hc1]
            exact le_trans ih' (bpe_pocl_cons_le x y x0 (y0 :: xs))
      · -- merge a b into z
        have ih := bpe_pocl_main a b z x y hx hy n xs out (by omega) hout
        have hz : bpe_pair_count x y (z :: out) ≤ bpe_pair_count x y out := by
          match out with
          | [] => simp [bpe_pair_count]
          | o :: out' =>
            have : ¬ (z = x ∧ o = y) := fun h => hx h.1.symm
            simp [bpe_pair_count, this]
        exact le_trans hz (le_trans ih (le_trans (bpe_pocl_cons_le x y y0 xs) (bpe_pocl_cons_le x y x0 (y0 :: xs))))

theorem bpe_partial_old_pair_count_le
    (a b z : ℕ) (s t : List ℕ) (hz : z ∉ s)
    (h : bpe_partial_merge a b z s t) (x y : ℕ) (hx : x ≠ z) (hy : y ≠ z) :
    bpe_pair_count x y t ≤ bpe_pair_count x y s := by
  exact bpe_pocl_main a b z x y hx hy s.length s t le_rfl h
