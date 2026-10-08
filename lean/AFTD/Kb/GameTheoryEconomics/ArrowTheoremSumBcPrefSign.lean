import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremBcPref
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign

/-!
# ArrowTheorem.sum_bcPref_sign

Topic: social_choice   Node: 81d6300396ea

Provenance: helper lemma. TCSlib, `ArrowTheorem.sum_bcPref_sign`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Balanced b-versus-c preferences over the six orderings. Consider the six strict orderings of three alternatives $a$, $b$, and $c$, indexed by $k
\in \{0,\dots,5\}$, and let $p(k)$ denote the $b$-versus-$c$ pairwise preference of
ordering $k$. Under the sign encoding $\sigma$, these preferences sum to zero across all
six orderings:
\[
  \sum_{k=0}^{5} \sigma\bigl(p(k)\bigr) = 0.
\]
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- The sum of bcPref signs over all 6 orderings is 0. -/
lemma ArrowTheorem.sum_bcPref_sign :
    ∑ k : Fin 6, boolToSign (bcPref k) = 0 := by
  simp only [Fin.sum_univ_six, bcPref, boolToSign]
  norm_num
