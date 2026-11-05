import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ChoreOppositePair

/-!
# chore_opposite_pair_card

Topic: fair_division   Node: 32a260aec48d

Provenance: helper lemma. arXiv:2611.04884, Section 4, line 731

Given implicit natural numbers m and n, a hypothesis h2n : 2 * n ≤ m, and an element j : Fin n, the cardinality of chore_opposite_pair h2n j is equal to 2.
-/

/-- Every opposite pair contains exactly two distinct chores. -/
lemma chore_opposite_pair_card {m n : ℕ} (h2n : 2 * n ≤ m) (j : Fin n) :
    (chore_opposite_pair h2n j).card = 2 := by
  unfold chore_opposite_pair
  dsimp only
  rw [Finset.card_pair]
  intro h
  simp only [Fin.mk.injEq] at h
  have hj : (j : ℕ) < n := j.isLt
  omega
