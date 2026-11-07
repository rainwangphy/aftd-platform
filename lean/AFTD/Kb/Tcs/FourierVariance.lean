import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff

/-!
# fourier_variance

Topic: combinatorics   Node: 890af5daf598

Provenance: formalization of a published result. Source: arXiv:2611.08289 Section 2.1 (line 360)

The Fourier variance $\mathrm{Var}(f)$ of a function $f : \{0,1\}^n \to \mathbb{R}$ is the sum of the squares of its non-empty Fourier--Walsh coefficients: $\mathrm{Var}(f) = \sum_{S \subseteq [n], S \neq \emptyset} \hat{f}(S)^2$.
-/

/-- The Fourier variance Var(f) = ∑_{S ≠ ∅} f̂(S)^2 of a Boolean function. -/
noncomputable def fourier_variance {n : ℕ} (f : BooleanAnalysis.BooleanFunc n) : ℝ := ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter Finset.Nonempty,
    BooleanAnalysis.fourierCoeff f S ^ 2
