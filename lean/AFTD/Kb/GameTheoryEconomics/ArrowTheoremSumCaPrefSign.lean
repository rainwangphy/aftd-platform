import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCaPref
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign

/-!
# ArrowTheorem.sum_caPref_sign

Topic: social_choice   Node: 20c9f8610ba6

Provenance: helper lemma. TCSlib, `ArrowTheorem.sum_caPref_sign`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Vanishing sum of signed $c$-vs-$a$ preferences. For each of the six strict orderings $k\in\{0,1,\dots,5\}$ of three alternatives, let
$b_k\in\mathrm{Bool}$ record the $c$-vs-$a$ preference of ordering $k$, and encode it as
a sign by $\sigma(b_k)=1$ when $b_k$ is false and $\sigma(b_k)=-1$ when $b_k$ is true.
Then these six signed preferences sum to zero:
\[
  \sum_{k=0}^{5} \sigma(b_k) = 0.
\]
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- The sum of caPref signs over all 6 orderings is 0. -/
lemma ArrowTheorem.sum_caPref_sign :
    ∑ k : Fin 6, boolToSign (caPref k) = 0 := by
  simp only [Fin.sum_univ_six, caPref, boolToSign]
  norm_num
