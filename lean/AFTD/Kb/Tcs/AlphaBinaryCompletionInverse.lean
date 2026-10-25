import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaBinaryPrefix
import AFTD.Kb.Tcs.AlphaBinaryPrefixBounds
import AFTD.Kb.Tcs.AlphaBinaryPrefixInverseParity
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcInverseConcat
import AFTD.Kb.Tcs.BrgcInverseFlipPreservesCutMax

/-!
# alpha_binary_completion_inverse

Topic: combinatorics   Node: 3b5474a4efbc

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

Completing the prefix to even or odd Hamming parity gives the two consecutive inverse Gray ranks 2q and 2q+1.
-/

theorem alpha_binary_completion_inverse (a : List ℕ)
    (ha : ∀ v ∈ a, 0 < v) :
    brgc_inverse (a.sum + 1) (2 * alpha_binary_prefix a + a.length % 2) =
      2 * brgc_inverse a.sum (alpha_binary_prefix a) ∧
    brgc_inverse (a.sum + 1) (2 * alpha_binary_prefix a + (a.length + 1) % 2) =
      2 * brgc_inverse a.sum (alpha_binary_prefix a) + 1 := by
  cases a with
  | nil => simp [alpha_binary_prefix, brgc_inverse]
  | cons v rest =>
    have hp : alpha_binary_prefix (v :: rest) < 2 ^ (v :: rest).sum :=
      (alpha_binary_prefix_bounds _ (by simp) ha).2
    have hpar : brgc_inverse (v :: rest).sum (alpha_binary_prefix (v :: rest)) % 2
        = (v :: rest).length % 2 := alpha_binary_prefix_inverse_parity _ ha
    have key : ∀ b : ℕ, b < 2 →
        brgc_inverse ((v :: rest).sum + 1) (2 * alpha_binary_prefix (v :: rest) + b)
          = 2 * brgc_inverse (v :: rest).sum (alpha_binary_prefix (v :: rest)) +
            (if (v :: rest).length % 2 = 0 then b else 1 - b) := by
      intro b hb
      have hc := brgc_inverse_concat (m := (v :: rest).sum) (k := 1)
        (a := alpha_binary_prefix (v :: rest)) (b := b) hp hb
      rw [hpar] at hc
      rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
      · simpa using hc
      · have h11 : brgc_inverse 1 1 = 1 := by rfl
        rw [h11] at hc
        simpa using hc
    have hb2 : (v :: rest).length % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rcases (by omega : (v :: rest).length % 2 = 0 ∨ (v :: rest).length % 2 = 1) with hc | hc
    · have h2 : ((v :: rest).length + 1) % 2 = 1 := by omega
      constructor
      · rw [hc, key 0 (by norm_num), if_pos hc]; simp
      · rw [h2, key 1 (by norm_num), if_pos hc]
    · have h2 : ((v :: rest).length + 1) % 2 = 0 := by omega
      constructor
      · rw [hc, key 1 (by norm_num), if_neg (by omega : ¬ (v :: rest).length % 2 = 0)]; simp
      · rw [h2, key 0 (by norm_num), if_neg (by omega : ¬ (v :: rest).length % 2 = 0)]
