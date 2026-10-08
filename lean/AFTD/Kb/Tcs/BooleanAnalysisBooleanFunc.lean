import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# BooleanAnalysis.BooleanFunc

Topic: combinatorics   Node: e83aafd7153d

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.BooleanFunc`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

A \emph{Boolean function} of arity $n$ is a function $f : \{0,1\}^n \to \bbr$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
/-- Defines a real-valued Boolean function `f : {0,1}ⁿ → ℝ`. **Source:** [OD14, §1.1]. -/
abbrev BooleanAnalysis.BooleanFunc (n : ℕ) := BoolCube n → ℝ
