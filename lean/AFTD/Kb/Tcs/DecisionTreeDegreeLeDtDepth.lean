import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisHasDegreeAtMost
import AFTD.Kb.Tcs.DtDepth
import AFTD.Kb.Tcs.DecisionTreeDegreeLeDepth
import AFTD.Kb.Tcs.DecisionTreeExistsDtreeOfDtDepth
import AFTD.Kb.Tcs.DecisionTreeSignEval
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignFalse
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignTrue
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignSq
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisSumBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignNot
import AFTD.Kb.Tcs.DecisionTree

/-!
# DecisionTree.degree_le_dtDepth

Topic: circuits   Node: c58a9bc3272c

Provenance: formalization of a published result. Source: Degree bounded by decision-tree depth, as formalized in TCSlib (`DecisionTree.degree_le_dtDepth`). Lean proof by Hydroxyi, Owen McGinty, Seyoon Ragavan (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean (Apache-2.0); 1 verbatim; compiled here.

Degree bounded by decision-tree depth. Let $f : \{0,1\}^n \to \{0,1\}$ be a Boolean-valued function, and let $D(f)$ denote its
decision-tree depth, the least $d$ for which some decision tree of depth at most $d$
computes $f$. Let $g : \{0,1\}^n \to \bbr$ be its sign encoding, $g(x) = \sigma(f(x))$,
where $\sigma$ sends $0$ to $1$ and $1$ to $-1$. Then $g$ has degree at most $D(f)$:
every set $S$ with $\hat g(S) \neq 0$ satisfies $\abs{S} \le D(f)$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
variable {n : ℕ} in
/-- **Proposition 3.16 for `dtDepth`**: the ±1-encoding of a Boolean function has Fourier degree at most its minimum decision-tree depth. This is the "DT(f) ≤ k ⇒ deg(f) ≤ k" input to O'Donnell Lemma 4.21. **Source:** [OD14, Prop. 3.16]. -/
theorem DecisionTree.degree_le_dtDepth (f : (Fin n → Bool) → Bool) :
    has_degree_at_most (fun x => boolToSign (f x)) (dtDepth f) := by
  obtain ⟨T, hdepth, heval⟩ := exists_dtree_of_dtDepth f
  have hfun : (fun x => boolToSign (f x)) = T.signEval := by
    funext x
    rw [signEval, heval x]
  rw [hfun]
  intro S hS
  exact le_trans (degree_le_depth T S hS) hdepth
