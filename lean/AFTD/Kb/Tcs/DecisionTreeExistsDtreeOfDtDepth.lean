import AFTD.Prelude
import AFTD.Kb.Tcs.DecisionTree
import AFTD.Kb.Tcs.DecisionTreeDepth
import AFTD.Kb.Tcs.DecisionTreeEval
import AFTD.Kb.Tcs.DtDepth

/-!
# DecisionTree.exists_dtree_of_dtDepth

Topic: circuits   Node: 72b97dce50cf

Provenance: helper lemma. TCSlib, `DecisionTree.exists_dtree_of_dtDepth`. Lean proof by Hydroxyi, Owen McGinty, Seyoon Ragavan (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean (Apache-2.0); 1 verbatim; compiled here.

Attainment of the decision-tree depth. For every Boolean function $f : (\mathrm{Fin}\,n \to \mathrm{Bool}) \to \mathrm{Bool}$,
there is a decision tree $T$ on the $n$ Boolean variables whose depth is at most the
decision-tree depth of $f$ and which computes $f$, meaning $T$ evaluates to $f(x)$ on
every input $x$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : ℕ} in
/-- Specification of `dtDepth`: some tree of depth `≤ dtDepth f` computes `f`. -/
lemma DecisionTree.exists_dtree_of_dtDepth (f : (Fin n → Bool) → Bool) :
    ∃ T : DecisionTree n, T.depth ≤ dtDepth f ∧ ∀ x, T.eval x = f x := by
  classical
  unfold dtDepth
  exact Nat.find_spec
    (p := fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x) _
