import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.DecisionTree
import AFTD.Kb.Tcs.DecisionTreeEval

/-!
# DecisionTree.signEval

Topic: circuits   Node: bb50e8a39751

Provenance: formalization of a published result. Source: TCSlib, `DecisionTree.signEval`. Lean proof by Hydroxyi, Owen McGinty, Seyoon Ragavan (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean (Apache-2.0); 1 verbatim; compiled here.

The $\pm 1$-valued function computed by a decision tree $T$, namely
$x \mapsto \mathrm{boolToSign}(T.\mathrm{eval}\,x)$, where $\mathrm{false} \mapsto 1$ and
$\mathrm{true} \mapsto -1$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
variable {n : ℕ} in
/-- The ±1-valued function computed by a decision tree (`false ↦ 1`, `true ↦ -1`, following `boolToSign`). -/
noncomputable def DecisionTree.signEval (T : DecisionTree n) : BooleanFunc n :=
  fun x => boolToSign (T.eval x)
