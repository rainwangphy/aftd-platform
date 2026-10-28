import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPos
import AFTD.Kb.GameTheoryEconomics.ArrowsUnmarked

/-!
# arrows_unmarked_decidable

Topic: combinatorial_games   Node: ea84d524b8da

Provenance: helper lemma. step towards arrows_op602_refutation_tree_grundy_gt_three

For a finite graph with decidable adjacency, whether u and v form an unmarked edge at p is decidable.
-/

/-- Decidability of the unmarked-edge predicate, so that legality can be settled by kernel `decide`. -/
instance arrows_unmarked_decidable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ArrowsPos V) (u v : V) : Decidable (ArrowsUnmarked G p u v) := by unfold ArrowsUnmarked; infer_instance
