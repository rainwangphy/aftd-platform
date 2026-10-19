import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTreeBind
import AFTD.Kb.Tcs.ComparisonTreeEval
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.ComparisonTree
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# comparison_tree_eval_bind

Topic: algorithms   Node: cf3d4a512899

Provenance: helper lemma. step towards v_selection_16_8_upper_bound

Running the composition `comparison_tree_bind T f` on a value assignment `v` gives the same index as running `T` on `v` and then running the continuation tree `f` on the index that `T` returned.
-/

/-- Evaluation of a composed tree: running `bind T f` is running `T` and then continuing with the branch selected by its answer. -/
theorem comparison_tree_eval_bind {n : ℕ} {α : Type*} [LinearOrder α] (v : Fin n → α)
    (T : ComparisonTree n) (f : Fin n → ComparisonTree n) :
    comparison_tree_eval v (comparison_tree_bind T f)
      = comparison_tree_eval v (f (comparison_tree_eval v T)) := by
  induction T with
  | leaf a => rfl
  | branch i j l r ihl ihr =>
    simp only [comparison_tree_bind, comparison_tree_eval]
    split
    · exact ihl
    · exact ihr
