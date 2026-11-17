import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869BoundedFuelMono
import AFTD.Kb.Tcs.Op869ExtendPredecessors
import AFTD.Kb.Tcs.Op869ExtendColors
import AFTD.Kb.Tcs.Op869BoundedVertexPadding

/-!
# op869_bounded_initial_vertex_mono

Topic: online_algorithms   Node: 0a13ccdf9bf2

Provenance: helper lemma. Padding and monotonicity for the finite adversary game of arXiv:2610.41516 Section 2.

For a positive colorability bound, an initially winning bounded adversary strategy remains winning on any larger vertex universe with its full move budget.
-/

/-- For a positive colorability bound, an initially winning bounded adversary strategy remains winning on any larger vertex universe with its full move budget. -/
theorem op869_bounded_initial_vertex_mono {n m : ℕ} (hnm : n ≤ m) (k t K D : ℕ) (hk : 1 ≤ k)
    (hwin : op869_bounded_adversary_forces k t K D n 0
      (fun _ : Fin n => ∅) (fun _ : Fin n => ∅)) :
    op869_bounded_adversary_forces k t K D m 0
      (fun _ : Fin m => ∅) (fun _ : Fin m => ∅) := by
  classical
  have hp := op869_bounded_vertex_padding hnm k t K D hk n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) hwin
  have hp0 : op869_extend_predecessors hnm (fun _ : Fin n => ∅) = (fun _ : Fin m => ∅) := by
    funext x
    simp [op869_extend_predecessors]
  have hc0 : op869_extend_colors hnm (fun _ : Fin n => ∅) = (fun _ : Fin m => ∅) := by
    funext x
    simp [op869_extend_colors]
  rw [hp0, hc0] at hp
  exact op869_bounded_fuel_mono k t K D n m 0 _ _ hnm hp
