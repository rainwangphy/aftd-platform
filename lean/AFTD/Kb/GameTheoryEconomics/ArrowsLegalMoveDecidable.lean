import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsIsSink
import AFTD.Kb.GameTheoryEconomics.ArrowsLegalMove
import AFTD.Kb.GameTheoryEconomics.ArrowsPos
import AFTD.Kb.GameTheoryEconomics.ArrowsUnmarked
import AFTD.Kb.GameTheoryEconomics.ArrowsIsSource

/-!
# arrows_legal_move_decidable

Topic: combinatorial_games   Node: b9d5fd261d9a

Provenance: helper lemma. step towards arrows_op602_refutation_tree_grundy_gt_three

For a finite graph with decidable equality and decidable adjacency, whether q is a legal option of p is decidable.
-/

/-- Decidability of the legal-move relation, so that concrete legality instances can be closed by kernel `decide`. -/
instance arrows_legal_move_decidable {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ArrowsPos V) : Decidable (ArrowsLegalMove G p q) := by unfold ArrowsLegalMove ArrowsUnmarked ArrowsIsSink ArrowsIsSource; infer_instance
