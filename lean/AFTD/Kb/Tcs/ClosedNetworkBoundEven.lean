import AFTD.Prelude
import AFTD.Kb.Tcs.ClosedNetworkBound

/-!
# closed_network_bound_even

Topic: quantum   Node: 39650ead7c06

Provenance: helper lemma. arXiv:2610.35838 Theorem 4

For any natural number n, if n is even, then closed_network_bound n = Real.sqrt 2.
-/

/-- For even n, the closed-network quantum bound is sqrt(2). -/
theorem closed_network_bound_even {n : ℕ} (hn : Even n) :
    closed_network_bound n = Real.sqrt 2 := by
  unfold closed_network_bound
  rw [if_pos hn]
