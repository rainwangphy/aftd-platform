import AFTD.Prelude
import AFTD.Kb.Tcs.HammingBall
import AFTD.Kb.Tcs.HammingRing

/-!
# disjoint_hamming_ball_hamming_ring_same

Topic: information   Node: 8683e612736b

Provenance: helper lemma. arXiv:2611.18156 Theorem III.3 proof

Given implicit parameters n and q, for any point x : Fin n → Fin q, the Hamming ball of radius c centered at x and the (c, c') Hamming ring centered at x are disjoint.
-/

/-- Hamming ball of radius c and (c, c') Hamming ring centered at the same point are disjoint. -/
theorem disjoint_hamming_ball_hamming_ring_same {n q : ℕ} (c c' : ℕ) (x : Fin n → Fin q) :
    Disjoint (hamming_ball c x) (hamming_ring c c' x) := by
  rw [Finset.disjoint_left]
  intro y hy1 hy2
  simp [hamming_ball] at hy1
  simp [hamming_ring] at hy2
  omega
