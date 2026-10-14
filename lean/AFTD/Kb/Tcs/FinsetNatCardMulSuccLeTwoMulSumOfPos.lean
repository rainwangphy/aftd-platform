import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetNatMulCardMulSuccLeTwoMulSum

/-!
# finset_nat_card_mul_succ_le_two_mul_sum_of_pos

Topic: combinatorics   Node: 96f0c915e6ad

Provenance: helper lemma. Step (3) of the proof of Lemma 1 in arXiv:2610.15860 (A note on the Slater–Vélez permutation).

The sum of q distinct positive integers is at least q(q+1)/2.
-/

theorem finset_nat_card_mul_succ_le_two_mul_sum_of_pos (S : Finset ℕ) (h : ∀ v ∈ S, 0 < v) :
    S.card * (S.card + 1) ≤ 2 * ∑ v ∈ S, v := open Finset in by
  have := finset_nat_mul_card_mul_succ_le_two_mul_sum 1 S (by
    intro v hv
    rw [one_mul]
    calc (S.filter (· ≤ v)).card ≤ (Icc 1 v).card := by
          apply card_le_card
          intro w hw
          rw [mem_filter] at hw
          exact mem_Icc.2 ⟨h w hw.1, hw.2⟩
      _ = v := by simp)
  simpa using this
