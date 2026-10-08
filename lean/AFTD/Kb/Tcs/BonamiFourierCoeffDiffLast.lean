import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct
import AFTD.Kb.Tcs.BonamiDiffLast
import AFTD.Kb.Tcs.BonamiRestrictLast
import AFTD.Kb.Tcs.BonamiUniformWeightSucc
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf

/-!
# Bonami.fourierCoeff_diffLast

Topic: combinatorics   Node: 0ee51bc1edaa

Provenance: helper lemma. TCSlib, `Bonami.fourierCoeff_diffLast`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 verbatim; compiled here.

Fourier coefficient of the half-difference over the last coordinate. Let $f\colon\{0,1\}^{n+1}\to\bbr$ be a Boolean function on $n+1$ variables, and let
$g\colon\{0,1\}^{n}\to\bbr$ be its half-difference over the last coordinate, given by
$g(x)=\tfrac12\bigl(f(x,0)-f(x,1)\bigr)$. For every frequency set
$S\subseteq\{1,\dots,n\}$, the Fourier--Walsh coefficient of $g$ at $S$ equals the
Fourier--Walsh coefficient of $f$ at the frequency set obtained by regarding $S$ as a
subset of the first $n$ coordinates of $\{1,\dots,n+1\}$ and adjoining the last
coordinate:
\[
  \hat g(S) \;=\; \hat f\bigl(S\cup\{n+1\}\bigr).
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
/-- The Fourier coefficient of `diffLast f` at `S` is the lifted coefficient containing the final coordinate. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.fourierCoeff_diffLast {n : ℕ} (f : BooleanFunc (n + 1)) (S : Finset (Fin n)) :
    BooleanAnalysis.fourierCoeff (diffLast f) S =
      BooleanAnalysis.fourierCoeff f (S.image Fin.castSucc ∪ {Fin.last n}) := by
  unfold diffLast BooleanAnalysis.fourierCoeff innerProduct expect chiS restrictLast
  rw [uniformWeight_succ]
  rw [show (Finset.univ : Finset (Fin (n + 1) → Bool)) =
    Finset.image (fun x : Fin n → Bool => Fin.snoc x Bool.false) Finset.univ ∪
      Finset.image (fun x : Fin n → Bool => Fin.snoc x Bool.true) Finset.univ from ?_,
    Finset.sum_union]
  · rw [Finset.sum_image, Finset.sum_image] <;>
      norm_num [Finset.prod_union, Finset.prod_image]
    ring_nf
    · simp +decide only [mul_assoc, Finset.sum_add_distrib, Finset.sum_mul _ _ _]
      rw [mul_add]
    · exact fun x y h => by simpa using congrArg Fin.init h
    · exact fun x y h => by simpa using congrArg Fin.init h
  · norm_num [Finset.disjoint_left]
  · ext x
    by_cases hx : x (Fin.last n) <;>
      simp +decide only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_and, true_iff]
    · exact Or.inr ⟨fun i => x i.castSucc, by
        ext i
        cases i using Fin.lastCases <;> aesop⟩
    · exact Or.inl ⟨fun i => x i.castSucc, by
        ext i
        cases i using Fin.lastCases <;> aesop⟩
