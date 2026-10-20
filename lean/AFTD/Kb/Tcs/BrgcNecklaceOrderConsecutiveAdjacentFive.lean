import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BrgcNecklaceFirstRank
import AFTD.Kb.Tcs.BitwordNecklaceAdjacent
import AFTD.Kb.Tcs.BitwordIsRotation
import AFTD.Kb.Tcs.BitwordRotate

/-!
# brgc_necklace_order_consecutive_adjacent_five

Topic: combinatorics   Node: a33e1c85028b

Provenance: formalization of a published result. Source: arXiv:2610.24758 (Optimal single-track Gray codes from Gray-ordered necklaces), Conjecture 1 (prime case of a conjecture from 2007), Sec. 1; the case n = 5, verified by computation in the paper

The case n = 5 of the conjecture: consecutive necklaces of D_5 are adjacent in Q_5.
-/

instance brgc_necklace_order_consecutive_adjacent_five_dec_is_rot (n x y : ℕ) :
    Decidable (bitword_is_rotation n x y) :=
  inferInstanceAs (Decidable (∃ r < n, (bitword_rotate n)^[r] x = y))

instance brgc_necklace_order_consecutive_adjacent_five_dec_first_rank (n t : ℕ) :
    Decidable (brgc_necklace_first_rank n t) :=
  inferInstanceAs (Decidable (t < 2 ^ n ∧ brgc_word t ≠ 0 ∧ brgc_word t ≠ 2 ^ n - 1 ∧
    ∀ s < t, ¬ bitword_is_rotation n (brgc_word s) (brgc_word t)))

instance brgc_necklace_order_consecutive_adjacent_five_dec_adj (n x y : ℕ) :
    Decidable (bitword_necklace_adjacent n x y) :=
  inferInstanceAs (Decidable (∃ r < n, ∃ i < n, (bitword_rotate n)^[r] x ^^^ y = 2 ^ i))

lemma brgc_necklace_order_consecutive_adjacent_five_fin :
    ∀ (t t' : Fin 32), brgc_necklace_first_rank 5 t.1 →
      brgc_necklace_first_rank 5 t'.1 → t.1 < t'.1 →
      (∀ s : Fin 32, t.1 < s.1 → s.1 < t'.1 → ¬ brgc_necklace_first_rank 5 s.1) →
      bitword_necklace_adjacent 5 (brgc_word t.1) (brgc_word t'.1) := by
  decide

theorem brgc_necklace_order_consecutive_adjacent_five :
    ∀ t t' : ℕ, brgc_necklace_first_rank 5 t →
      brgc_necklace_first_rank 5 t' → t < t' →
      (∀ s, t < s → s < t' → ¬ brgc_necklace_first_rank 5 s) →
      bitword_necklace_adjacent 5 (brgc_word t) (brgc_word t') := by
  intro t t' ht ht' hlt hbetween
  have ht_lt : t < 32 := ht.1
  have ht'_lt : t' < 32 := ht'.1
  exact brgc_necklace_order_consecutive_adjacent_five_fin ⟨t, ht_lt⟩ ⟨t', ht'_lt⟩ ht ht' hlt
    (fun s hs1 hs2 => hbetween s.1 hs1 hs2)
