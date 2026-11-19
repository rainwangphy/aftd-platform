import AFTD.Prelude
import AFTD.Kb.Tcs.LaplacianBoundingEntry

/-!
# has_laplacian_peak_state_transfer

Topic: graphs   Node: 8704ac2086d4

Provenance: formalization of a published result. Source: arXiv:2611.21567, Section 2

A simple graph G admits Laplacian peak state transfer between vertices u and v if there exists a real time t at which the absolute value of the (u,v)-entry of exp(i * t * L) equals the bounding matrix entry (B_L)_{u,v}.
-/

/-- Predicate that G admits Laplacian peak state transfer between u and v. -/
def has_laplacian_peak_state_transfer
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Prop :=
  ∃ t : ℝ,
    ‖NormedSpace.exp (Complex.I • (t : ℂ) • (G.lapMatrix ℂ)) u v‖ =
      laplacian_bounding_entry G u v
