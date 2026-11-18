import AFTD.Prelude
import AFTD.Kb.Tcs.TriangularNumber

/-!
# speed_robust_bricks_total_completion_time

Topic: online_algorithms   Node: ba5b92801e0f

Provenance: formalization of a published result. Source: arXiv:2611.20795 Section 2

Defines speed_robust_bricks_total_completion_time σ for an assignment σ : Fin n → Fin m of n unit-size jobs to m machines as the sum over all machines i : Fin m of triangular_number applied to the number of jobs assigned to machine i, that is, (Finset.univ.filter (fun j => σ j = i)).card.
-/

/-- The total completion time of n unit-size jobs assigned to m machines by σ. -/
def speed_robust_bricks_total_completion_time {n m : ℕ} (σ : Fin n → Fin m) : ℕ := ∑ i : Fin m, triangular_number (Finset.card (Finset.univ.filter (fun j => σ j = i)))
