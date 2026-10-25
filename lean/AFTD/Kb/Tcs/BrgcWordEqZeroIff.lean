import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord

/-!
# brgc_word_eq_zero_iff

Topic: combinatorics   Node: 82df59bc56d1

Provenance: helper lemma. Supporting arithmetic and canonical-representative lemmas for OP-392, arXiv:2610.24758, Conjecture 1.

The zero word is encoded exactly by rank zero.
-/

theorem brgc_word_eq_zero_iff (t : ℕ) : brgc_word t = 0 ↔ t = 0 := by
  constructor
  · intro h
    have hsame : t = t / 2 := Nat.eq_of_xor_eq_zero h
    by_contra hn
    have := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (show 1 < 2 by decide)
    omega
  · rintro rfl
    rfl
