import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignNot
import AFTD.Kb.Tcs.BooleanAnalysisChiS

/-!
# BooleanAnalysis.chiS_neg

Topic: combinatorics   Node: 5b3c01539406

Provenance: helper lemma. TCSlib, `BooleanAnalysis.chiS_neg`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Walsh character under global bit flip. Let $n$ be a natural number, let $S \subseteq [n]$, and let $x \in \{0,1\}^n$. Writing
$\lnot x$ for the point obtained by flipping every coordinate of $x$, the Walsh--Fourier
character $\chi_S$ satisfies
\[
  \chi_S(\lnot x) \;=\; (-1)^{\abs{S}}\,\chi_S(x),
\]
where $\abs{S}$ is the number of elements of $S$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Flipping all bits of `x` multiplies `χ_S(x)` by `(-1)^|S|`. -/
lemma BooleanAnalysis.chiS_neg (S : Finset (Fin n)) (x : BoolCube n) :
    chiS S (fun i => !x i) = (-1 : ℝ) ^ S.card * chiS S x := by
  simp only [chiS]
  simp_rw [boolToSign_not]
  -- ∏_{i∈S} (-boolToSign (x i)) = (-1)^|S| * ∏_{i∈S} boolToSign (x i)
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Finset.prod_insert ha, ih]
    ring
