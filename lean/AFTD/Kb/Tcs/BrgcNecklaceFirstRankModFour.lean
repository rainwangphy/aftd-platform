import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcNecklaceFirstRankWordOdd
import AFTD.Kb.Tcs.BrgcNecklaceFirstRank
import AFTD.Kb.Tcs.BrgcWord

/-!
# brgc_necklace_first_rank_mod_four

Topic: combinatorics   Node: ea4c2085b606

Provenance: helper lemma. Supporting arithmetic and canonical-representative lemmas for OP-392, arXiv:2610.24758, Conjecture 1.

For length at least two, each first-occurrence rank of a nonconstant necklace is congruent to one or two modulo four.
-/

theorem brgc_necklace_first_rank_mod_four {n t : ℕ} (hn : 2 ≤ n)
    (ht : brgc_necklace_first_rank n t) : t % 4 = 1 ∨ t % 4 = 2 := by
  have hodd := brgc_necklace_first_rank_word_odd hn ht
  have hx : brgc_word t % 2 = (t % 2) ^^^ ((t / 2) % 2) :=
    Nat.xor_mod_two_pow (n := 1)
  by_contra h
  have hcases : t % 4 = 0 ∨ t % 4 = 3 := by omega
  rcases hcases with hzero | hthree
  · have ha : t % 2 = 0 := by omega
    have hb : t / 2 % 2 = 0 := by omega
    simp [ha, hb, hodd] at hx
  · have ha : t % 2 = 1 := by omega
    have hb : t / 2 % 2 = 1 := by omega
    simp [ha, hb, hodd] at hx
