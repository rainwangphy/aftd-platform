import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SeededSubtractionSeq

/-!
# seeded_subtraction_seq_initial

Topic: combinatorial_games   Node: 8a603b38d43a

Provenance: helper lemma. knowledgebase, OP-1251

The value of the seeded subtraction sequence at any index $i < 2a + 1$ is equal to the corresponding seed value $\text{seed}(i)$.
-/

/-- The initial window of length 2a+1 of the seeded subtraction sequence coincides with the seed. -/
theorem seeded_subtraction_seq_initial (a : ℕ) (seed : Fin (2 * a + 1) → Bool) (i : Fin (2 * a + 1)) :
    seeded_subtraction_seq a seed i.val = seed i := by
  rw [seeded_subtraction_seq.eq_1, dif_pos i.isLt]
