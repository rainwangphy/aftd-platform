import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# ArrowTheorem.unanimity

Topic: social_choice   Node: 9d6ce1c7cc35

Provenance: formalization of a published result. Source: TCSlib, `ArrowTheorem.unanimity`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

A social welfare function $f:\{0,1\}^n\to\bbr$ is \emph{unanimous} if
$f(\texttt{false},\dots,\texttt{false}) = 1$: when all voters prefer
alternative $a$ over $b$, so does society.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- Unanimity: if all voters prefer a to b, society prefers a to b. In our encoding, f(all-false) = 1 means "a preferred to b" when every voter marks `false` (i.e., prefers the first alternative). **Source:** [OD14, Ch. 2]. -/
def ArrowTheorem.unanimity (f : BooleanFunc n) : Prop :=
  f (fun _ => false) = 1
