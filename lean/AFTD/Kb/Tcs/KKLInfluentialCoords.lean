import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInfluence

/-!
# KKL.influentialCoords

Topic: combinatorics   Node: 8896fdf41ff4

Provenance: formalization of a published result. Source: TCSlib, `KKL.influentialCoords`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

The set of $\tau$-\emph{influential} coordinates of $f$ is the finite set
\[
  J_\tau(f) \;=\; \{\, i \in [n] : \mathrm{Inf}_i[f] \ge \tau \,\}.
\]
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
/-- The set of `tau`-influential coordinates: `J_tau(f) = {i : Fin n | Inf_i[f] >= tau}`. **Source:** [OD14, Ch. 10]. -/
noncomputable def KKL.influentialCoords (f : BooleanFunc n) (τ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => τ ≤ influence i f)
