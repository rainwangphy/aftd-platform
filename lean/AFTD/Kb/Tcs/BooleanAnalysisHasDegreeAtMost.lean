import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff

/-!
# BooleanAnalysis.has_degree_at_most

Topic: combinatorics   Node: 609989f89260

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.has_degree_at_most`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 adapted; compiled here.

A Boolean function $f$ \emph{has degree at most $k$} if every nonzero Fourier
coefficient is supported on a set of size at most $k$: for all $S$, if
$\hat f(S)\ne 0$ then $|S|\le k$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Defines the predicate that a Boolean function has Fourier degree at most `k`. **Source:** [OD14, §1.3]. -/
def BooleanAnalysis.has_degree_at_most {n : ℕ} (f : (BooleanFunc n)) (k : ℕ) : Prop :=
  ∀ S, (BooleanAnalysis.fourierCoeff f S) ≠ 0 → S.card ≤ k
