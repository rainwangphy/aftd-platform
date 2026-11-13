import AFTD.Prelude
import AFTD.Kb.Tcs.MaxInducedLinearForest
import AFTD.Kb.Tcs.WienerIndex

/-!
# delta

Topic: graphs   Node: 311bf50fc8a6

Provenance: formalization of a published result. Source: arXiv:2611.12781, Section 2, equation (164)

For a finite simple graph G on vertex type V, delta G is the integer (max_induced_linear_forest G : ℤ) * (Fintype.card V : ℤ) * ((Fintype.card V : ℤ) - 1) - 4 * (wiener_index G : ℤ).
-/

/-- The deficit invariant delta(G) = L(G) * n * (n - 1) - 4 * W(G). -/
noncomputable def delta {V : Type*} [Fintype V] (G : SimpleGraph V) : ℤ := (max_induced_linear_forest G : ℤ) * (Fintype.card V : ℤ) * ((Fintype.card V : ℤ) - 1) - 4 * (wiener_index G : ℤ)
