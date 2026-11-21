import AFTD.Prelude

/-!
# op_2130_coin_blocks_avoid_count

Topic: online_algorithms   Node: 20e8d3ae959b

Provenance: helper lemma. Independent-block counterexample to op_2130_path_greedy_fixed_time_tail

For N blocks of L Boolean coins and any fixed L-coin tape, the number of block assignments in which every block differs from that tape is exactly (2^L − 1)^N.
-/

theorem op_2130_coin_blocks_avoid_count (N L : ℕ) (coin : Fin L → Bool) :
    (Finset.univ.filter (fun f : Fin N → (Fin L → Bool) => ∀ i, f i ≠ coin)).card =
      (2 ^ L - 1) ^ N := by
  classical
  have h : (Finset.univ.filter (fun f : Fin N → (Fin L → Bool) => ∀ i, f i ≠ coin)) =
      Fintype.piFinset (fun _ : Fin N => Finset.univ.erase coin) := by
    ext f
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset_const, Finset.card_erase_of_mem (Finset.mem_univ coin)]
  simp
