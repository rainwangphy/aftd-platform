import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolDiscrepancies
import AFTD.Kb.Tcs.MaxVertexDiscrepancy

/-!
# carpool_max_discrepancy

Topic: online_algorithms   Node: f27b772933a3

Provenance: formalization of a published result. Source: arXiv:2611.00388 Eq (1.2), Online carpooling against an oblivious adversary

The maximum discrepancy M_T over all time steps 0 ≤ t ≤ T of the maximum vertex discrepancy.
-/

/-- The maximum prefix discrepancy M_T of an online carpooling trajectory. -/
def carpool_max_discrepancy (n : ℕ) (edges : List (Fin n × Fin n)) (signs : List Bool) : ℕ := ((carpool_discrepancies n edges signs).map (max_vertex_discrepancy n)).foldl max 0
