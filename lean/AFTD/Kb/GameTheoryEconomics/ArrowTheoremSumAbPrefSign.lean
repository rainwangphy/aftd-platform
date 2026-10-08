import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremAbPref
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign

/-!
# ArrowTheorem.sum_abPref_sign

Topic: social_choice   Node: 8e5bb7534fd4

Provenance: helper lemma. TCSlib, `ArrowTheorem.sum_abPref_sign`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Balance of the a-vs-b preference signs. There are six strict orderings $k \in \{0,1,\dots,5\}$ of the three alternatives
$a,b,c$. For each such ordering, let $p_{ab}(k)$ be its $a$-vs-$b$ preference, the
Boolean that records whether $b$ is ranked above $a$, and apply the sign encoding
$\sigma$, so that $\sigma(p_{ab}(k))$ equals $+1$ when ordering $k$ ranks $a$ above $b$
and $-1$ when it ranks $b$ above $a$. Then these six signed preferences sum to zero:
\[
  \sum_{k=0}^{5} \sigma\bigl(p_{ab}(k)\bigr) = 0.
\]
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- The sum of abPref signs over all 6 orderings is 0. -/
lemma ArrowTheorem.sum_abPref_sign :
    ∑ k : Fin 6, boolToSign (abPref k) = 0 := by
  simp only [Fin.sum_univ_six, abPref, boolToSign]
  norm_num
