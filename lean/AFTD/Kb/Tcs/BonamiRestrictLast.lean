import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# Bonami.restrictLast

Topic: combinatorics   Node: acaa007414ea

Provenance: formalization of a published result. Source: TCSlib, `Bonami.restrictLast`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 verbatim; compiled here.

Given a Boolean function $f$ on $n+1$ variables and a bit $b$, the restriction
$\mathrm{restrictLast}\,f\,b$ is the function on $n$ variables obtained by fixing the last
coordinate to $b$, i.e.\ $x \mapsto f(x, b)$.
-/

open BooleanAnalysis in
/-- Restricts a Boolean function by fixing its final coordinate. **Source:** [OD14, Cor. 9.6 (proof)]. -/
noncomputable def Bonami.restrictLast {n : ℕ} (f : BooleanFunc (n + 1)) (b : Bool) : BooleanFunc n :=
  fun x => f (Fin.snoc x b)
