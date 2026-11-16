import AFTD.Prelude
import AFTD.Kb.Tcs.HammingBall
import AFTD.Kb.Tcs.HammingRing

/-!
# hamming_ring_subset_ball

Topic: information   Node: 84c64f661538

Provenance: helper lemma. arXiv:2611.18156 Section III

Given implicit parameters n and q, for any x : Fin n → Fin q, the (c, c') Hamming ring centered at x is a subset of the Hamming ball of radius c + c' centered at x.
-/

/-- The (c, c') Hamming ring centered at x is a subset of the Hamming ball of radius c + c' centered at x. -/
theorem hamming_ring_subset_ball {n q : ℕ} (c c' : ℕ) (x : Fin n → Fin q) :
    hamming_ring c c' x ⊆ hamming_ball (c + c') x := by
  intro y hy
  simp only [hamming_ring, hamming_ball, Finset.mem_filter, Finset.mem_univ,
    true_and] at hy ⊢
  exact hy.2
