import AFTD.Prelude
import AFTD.Kb.Tcs.DiamondMove
import AFTD.Kb.Tcs.DiffersInOnePosition
import AFTD.Kb.Tcs.MaximalChainLowerSet
import AFTD.Kb.Tcs.ChainStepElement

/-!
# not_diamond_move_self

Topic: combinatorics   Node: 0c25f8e8119e

Provenance: helper lemma. folklore

No maximal chain of order ideals M of type MaximalChainLowerSet P has a diamond move to itself under any labeling l : P → Fin (Fintype.card P).
-/

/-- Irreflexivity of diamond moves. -/
theorem not_diamond_move_self {P : Type*} [PartialOrder P] [Fintype P]
    (l : P → Fin (Fintype.card P)) (M : MaximalChainLowerSet P) :
    ¬ diamond_move l M M := by
  rintro ⟨i, hi, hdiff, -⟩
  exact hdiff.1 rfl
