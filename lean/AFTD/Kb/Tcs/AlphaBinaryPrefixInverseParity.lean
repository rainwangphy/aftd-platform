import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaBinaryPrefix
import AFTD.Kb.Tcs.AlphaBinaryPrefixBounds
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcInverseConcat
import AFTD.Kb.Tcs.BrgcInverseWord
import AFTD.Kb.Tcs.BrgcWordLowOnes
import AFTD.Kb.Tcs.BrgcInverseLtTwoPow
import AFTD.Kb.Tcs.BrgcInverseFlipPreservesCutMax
import AFTD.Kb.Tcs.BrgcWord

/-!
# alpha_binary_prefix_inverse_parity

Topic: combinatorics   Node: a7fc42861388

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

The inverse Gray rank of the prefix has the parity of the number of encoded one bits, namely the cell count.
-/

theorem alpha_binary_prefix_inverse_parity (a : List ℕ)
    (ha : ∀ v ∈ a, 0 < v) :
    brgc_inverse a.sum (alpha_binary_prefix a) % 2 = a.length % 2 := by
  induction a with
  | nil =>
    simp only [List.sum_nil, List.length_nil, alpha_binary_prefix]
    decide
  | cons x xs ih =>
    have hx : 0 < x := ha x (by simp)
    have hxs : ∀ v ∈ xs, 0 < v := fun v hv => ha v (List.mem_cons_of_mem _ hv)
    rw [List.sum_cons, List.length_cons]
    have hcons : alpha_binary_prefix (x :: xs) = 2 ^ xs.sum * 2 ^ (x - 1) + alpha_binary_prefix xs := by
      simp only [alpha_binary_prefix]
      rw [show x - 1 + xs.sum = xs.sum + (x - 1) by omega, pow_add]
    rw [hcons]
    have hfirst : 2 ^ (x - 1) < 2 ^ x := by
      apply Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hlt : alpha_binary_prefix xs < 2 ^ xs.sum := by
      rcases xs with _ | ⟨y, ys⟩
      · simp [alpha_binary_prefix]
      · exact (alpha_binary_prefix_bounds (y :: ys) (by simp) (fun v hv => hxs v (by simp [hv]))).2
    rw [brgc_inverse_concat (m := x) (k := xs.sum) (a := 2 ^ (x - 1))
      (b := alpha_binary_prefix xs) hfirst hlt]
    have hrank : brgc_inverse x (2 ^ (x - 1)) = 2 ^ x - 1 := by
      have hw : brgc_word (2 ^ x - 1) = 2 ^ (x - 1) := by
        have h := brgc_word_low_ones (x - 1)
        rwa [show x - 1 + 1 = x by omega] at h
      rw [← hw]
      exact brgc_inverse_word (by have := Nat.two_pow_pos x; omega)
    have hodd : (2 ^ x - 1) % 2 = 1 := by
      have h2 : 2 ^ x % 2 = 0 := by
        rw [Nat.pow_mod]
        have : 2 % 2 = 0 := by norm_num
        rw [this]
        simp [Nat.pos_iff_ne_zero.mp hx]
      have hge : 1 ≤ 2 ^ x := Nat.one_le_two_pow
      omega
    rw [hrank, if_neg (by rw [hodd]; norm_num)]
    rcases xs with _ | ⟨y, ys⟩
    · simp [alpha_binary_prefix, hodd]
    · have hy : 0 < y := hxs y (by simp)
      have hk : 0 < (y :: ys).sum := by
        rw [List.sum_cons]; omega
      set E := 2 ^ (y :: ys).sum with hEdef
      set R := brgc_inverse (y :: ys).sum (alpha_binary_prefix (y :: ys)) with hRdef
      have hEeven : E % 2 = 0 := by
        rw [hEdef]
        have h2 : 2 ^ (y :: ys).sum = 2 ^ ((y :: ys).sum - 1) * 2 := by
          rw [← pow_succ]
          congr 1
          omega
        rw [h2, Nat.mul_mod]
        simp
      have hEmul : (E * (2 ^ x - 1)) % 2 = 0 := by
        rw [Nat.mul_mod, hEeven]
        simp
      have hRlt : R < E := by
        rw [hRdef, hEdef]
        apply brgc_inverse_lt_two_pow
        exact (alpha_binary_prefix_bounds (y :: ys) (by simp)
          (fun v hv => hxs v (by simp [hv]))).2
      have hsub : (E - 1 - R) % 2 = (R + 1) % 2 := by
        have hE2 : 2 ≤ E := by omega
        have h1 : E - 1 - R = E - (R + 1) := by omega
        rw [h1]
        omega
      have ih' : R % 2 = (y :: ys).length % 2 := ih (fun v hv => hxs v (by simp [hv]))
      rw [Nat.add_mod, hEmul, hsub]
      omega
