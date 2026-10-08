import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight

/-!
# Bonami.uniformWeight_succ

Topic: combinatorics   Node: 83b4836b517d

Provenance: helper lemma. TCSlib, `Bonami.uniformWeight_succ`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 verbatim; compiled here.

Uniform weight halves with each added coordinate. For every natural number $n$, the uniform weight $2^{-n}$ assigned to each point of
$\{0,1\}^n$ satisfies \[2^{-(n+1)} = \frac{2^{-n}}{2},\] so that the uniform weight on
the cube of one higher dimension is half the uniform weight on the original cube.
-/

open BooleanAnalysis in
/-- Computes the uniform weight of an `(n + 1)`-dimensional Boolean cube. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.uniformWeight_succ (n : ℕ) :
    uniformWeight (n + 1) = uniformWeight n / 2 := by
  simp [uniformWeight, pow_succ]
  ring
