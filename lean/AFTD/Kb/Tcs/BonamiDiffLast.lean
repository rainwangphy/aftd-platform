import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BonamiRestrictLast

/-!
# Bonami.diffLast

Topic: combinatorics   Node: 333d5919b5b6

Provenance: formalization of a published result. Source: TCSlib, `Bonami.diffLast`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 verbatim; compiled here.

The half-difference $\mathrm{diffLast}\,f$ of $f$ over its last coordinate is the function on
$n$ variables given by $\tfrac12\bigl(\mathrm{restrictLast}\,f\,\mathrm{false} - \mathrm{restrictLast}\,f\,\mathrm{true}\bigr)$.
-/

open BooleanAnalysis in
/-- Defines the half-difference of a Boolean function over its final coordinate. **Source:** [OD14, Cor. 9.6 (proof)]. -/
noncomputable def Bonami.diffLast {n : ℕ} (f : BooleanFunc (n + 1)) : BooleanFunc n :=
  fun x => (restrictLast f false x - restrictLast f true x) / 2
