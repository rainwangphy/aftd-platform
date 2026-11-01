import AFTD.Prelude
import AFTD.Kb.Tcs.OpenNetworkBound

/-!
# open_network_bound_even

Topic: quantum   Node: 69dd5be316ac

Provenance: helper lemma. arXiv:2610.35838 Theorem 4

For any natural number n, if n is even, then open_network_bound n = 2.
-/

/-- For even n, the open-network quantum bound is 2. -/
theorem open_network_bound_even {n : ℕ} (hn : Even n) :
    open_network_bound n = 2 := by
  simp [open_network_bound, hn]
