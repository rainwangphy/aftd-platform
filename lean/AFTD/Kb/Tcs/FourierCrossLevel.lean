import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff

/-!
# fourier_cross_level

Topic: combinatorics   Node: 05e3d2afc75b

Provenance: formalization of a published result. Source: arXiv:2611.08289 Section 2.1 (equation (13), line 358)

The $k$-th cross Fourier level $W_k[f,g]$ of two real-valued functions $f, g : \{0,1\}^n \to \mathbb{R}$ is the sum $\sum_{|S|=k} \hat{f}(S)\hat{g}(S)$ over all subsets $S \subseteq [n]$ of cardinality $k$, where $\hat{f}(S)$ and $\hat{g}(S)$ are the Fourier--Walsh coefficients.
-/

/-- The k-th cross Fourier level W_k[f,g] = ∑_{|S|=k} f̂(S)ĝ(S) of two Boolean functions. -/
noncomputable def fourier_cross_level {n : ℕ} (k : ℕ) (f g : BooleanAnalysis.BooleanFunc n) : ℝ := ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
    BooleanAnalysis.fourierCoeff f S * BooleanAnalysis.fourierCoeff g S
