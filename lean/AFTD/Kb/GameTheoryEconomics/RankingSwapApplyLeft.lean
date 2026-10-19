import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RankingSwap

/-!
# ranking_swap_apply_left

Topic: fair_division   Node: 68efc8d4cf2c

Provenance: helper lemma. Sanity lemma for ranking_swap (arXiv:2610.23040 Definition 3.5).

After swapping positions k and l, position k holds the good that was at position l.
-/

theorem ranking_swap_apply_left {G : Type*} {m : ℕ} (r : Fin m ≃ G) (k l : Fin m) :
    ranking_swap r k l k = r l := by
  simp [ranking_swap]
