import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BonamiAvgLast
import AFTD.Kb.Tcs.BonamiDiffLast
import AFTD.Kb.Tcs.BonamiRestrictLast

/-!
# Bonami.restrictLast_true_eq

Topic: combinatorics   Node: d94e56664176

Provenance: helper lemma. TCSlib, `Bonami.restrictLast_true_eq`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 verbatim; compiled here.

Recovering the true-restriction from average and half-difference. Let $f : \{0,1\}^{n+1} \to \bbr$ be a Boolean function on $n+1$ variables. For a bit
$b$, write $f_b : \{0,1\}^n \to \bbr$ for the restriction $x \mapsto f(x,b)$ that fixes
the last coordinate to $b$, and let its average and half-difference over the last
coordinate be the functions $\tfrac12(f_0 + f_1)$ and $\tfrac12(f_0 - f_1)$. Then for
every point $x \in \{0,1\}^n$, the restriction fixing the last coordinate to
$\mathrm{true}$ equals the average minus the half-difference at that point:
\[
f_1(x) \;=\; \tfrac12\bigl(f_0(x) + f_1(x)\bigr) \;-\; \tfrac12\bigl(f_0(x) -
f_1(x)\bigr).
\]
-/

open BooleanAnalysis in
/-- States that the `true` restriction is the average minus the half-difference part. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.restrictLast_true_eq {n : ℕ} (f : BooleanFunc (n + 1)) (x : BoolCube n) :
    restrictLast f true x = avgLast f x - diffLast f x := by
  simp [restrictLast, avgLast, diffLast]
  ring
