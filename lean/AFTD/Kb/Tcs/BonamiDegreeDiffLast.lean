import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisHasDegreeAtMost
import AFTD.Kb.Tcs.BonamiDiffLast
import AFTD.Kb.Tcs.BonamiFourierCoeffDiffLast
import AFTD.Kb.Tcs.BooleanAnalysisInstAddCommGroupBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInstModuleRealBooleanFunc

/-!
# Bonami.degree_diffLast

Topic: combinatorics   Node: c7f5563f6b50

Provenance: helper lemma. TCSlib, `Bonami.degree_diffLast`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 adapted; compiled here.

Degree bound for the half-difference over the last coordinate. Let $f\colon\{0,1\}^{n+1}\to\bbr$ be a Boolean function of degree at most $k$, meaning
that every frequency set $S$ with nonzero Fourier--Walsh coefficient $\hat f(S)\ne 0$
satisfies $\abs{S}\le k$. Write $f_0$ and $f_1$ for the two restrictions of $f$ to
$\{0,1\}^{n}$ obtained by fixing its last coordinate to $0$ and to $1$ respectively, and
let $g=\tfrac12(f_0-f_1)$ be the half-difference of $f$ over that coordinate. Then $g$
is a Boolean function on $\{0,1\}^{n}$ of degree at most $k-1$, with $k-1$ interpreted
as $0$ when $k=0$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
/-- Shows that the final-coordinate half-difference lowers a Fourier degree bound by one. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.degree_diffLast {n : ℕ} (f : BooleanFunc (n + 1)) (k : ℕ)
    (hf : has_degree_at_most f k) :
    has_degree_at_most (diffLast f) (k - 1) := by
  have h_fourier_coeff : ∀ S : Finset (Fin n),
      BooleanAnalysis.fourierCoeff (diffLast f) S =
        BooleanAnalysis.fourierCoeff f (Finset.image Fin.castSucc S ∪ {Fin.last n}) := by
    exact fourierCoeff_diffLast f
  intro S hS_nonzero
  have h_card : S.card + 1 ≤ k := by
    have := hf (Finset.image Fin.castSucc S ∪ {Fin.last n})
    simp_all +decide [Finset.card_image_of_injective _ (Fin.castSucc_injective _)]
  exact Nat.le_sub_one_of_lt h_card
