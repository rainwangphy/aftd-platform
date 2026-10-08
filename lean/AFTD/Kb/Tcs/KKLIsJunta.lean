import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# KKL.IsJunta

Topic: combinatorics   Node: d8fb8aab6b68

Provenance: formalization of a published result. Source: TCSlib, `KKL.IsJunta`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

A function $g$ is a \emph{$J$-junta} if it depends only on the coordinates in $J$:
whenever $x$ and $y$ agree on every $i \in J$, we have $g(x) = g(y)$.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
/-- Defines a `J`-junta as a function depending only on coordinates in `J`. **Source:** [OD14, Ch. 10]. -/
def KKL.IsJunta (g : BooleanFunc n) (J : Finset (Fin n)) : Prop :=
  ∀ x y : BoolCube n, (∀ i ∈ J, x i = y i) → g x = g y
