import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisDictator

/-!
# ArrowTheorem.isDictator

Topic: social_choice   Node: 37a37c67a760

Provenance: formalization of a published result. Source: TCSlib, `ArrowTheorem.isDictator`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

$f$ is a \emph{dictatorship} if there exists a voter $i$ such that
$f = \mathrm{dict}_i$, i.e.\ society's preference always equals voter $i$'s.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- f is a dictatorship: there exists some voter i whose preference always determines society's preference. **Source:** [OD14, Ch. 2]. -/
def ArrowTheorem.isDictator (f : BooleanFunc n) : Prop :=
  ∃ i : Fin n, f = dictator i
