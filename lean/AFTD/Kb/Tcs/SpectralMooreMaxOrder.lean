import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralMooreSecondEigenvalueLe

/-!
# spectral_moore_max_order

Topic: graphs   Node: 24a501fb677e

Provenance: formalization of a published result. Source: arXiv:2611.00591 (A spectral Moore problem and the Yang-Koolen conjecture), Sec. 1 (definition of v(k, θ)); infinite values allowed, as in the paper's remark that v(k, θ) is infinite for θ ≥ 2√(k−1).

v(k, θ): the maximum number of vertices of a connected k-regular finite simple graph whose second largest adjacency eigenvalue is at most θ, as an extended natural number (⊤ when there are such graphs of every large order).
-/

/-- `v(k, θ)`: the maximum order of a connected `k`-regular simple graph whose second largest adjacency eigenvalue is at most `θ` (`⊤` when the orders are unbounded). -/
noncomputable def spectral_moore_max_order (k : ℕ) (θ : ℝ) : ℕ∞ := open Classical in
  ⨆ (n : ℕ) (G : SimpleGraph (Fin n))
    (_ : G.Connected ∧ G.IsRegularOfDegree k ∧ spectral_moore_second_eigenvalue_le G θ), (n : ℕ∞)
