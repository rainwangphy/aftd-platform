import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolStep

/-!
# carpool_discrepancies

Topic: online_algorithms   Node: 3db496b11597

Provenance: formalization of a published result. Source: arXiv:2611.00388 Eq (1.1), Online carpooling against an oblivious adversary

The sequence of discrepancy vectors (d₀, ..., d_T) starting from the zero vector, where each d_t is updated from d_{t-1} using the t-th edge and its orientation sign.
-/

/-- The trajectory of discrepancy vectors from time 0 to T for an edge sequence and signs. -/
def carpool_discrepancies (n : ℕ) (edges : List (Fin n × Fin n)) (signs : List Bool) :
    List (Fin n → ℤ) := (edges.zip signs).scanl (fun d (e, b) => carpool_step n d e b) (fun _ => 0)
