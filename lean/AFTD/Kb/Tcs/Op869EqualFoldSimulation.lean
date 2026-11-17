import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedInitialVertexMono
import AFTD.Kb.Tcs.Op869BoundedAdversaryForcesMonoDegree
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces

/-!
# op869_equal_fold_simulation

Topic: online_algorithms   Node: 5a72ae8ce335

Provenance: helper lemma. The t=q boundary case of the simulation inequality in arXiv:2610.41516 Lemma 2.5.

The fold-simulation conclusion holds in the case t=q: its numerical bounds are large enough to pad the board and relax the post-degree budget.
-/

/-- The equal-fold boundary case of the online-coloring simulation. -/
theorem op869_equal_fold_simulation (C n q K D n' D' : ℕ) (hC : 1 ≤ C) (hq : 1 ≤ q)
    (hqK : q ≤ K) (hD : 1 ≤ D)
    (hgame : op869_bounded_adversary_forces 3 q K D n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅))
    (hn : C*K^2*q*n*D*2^(C*((q+q-1)/q)) ≤ n')
    (hD' : C*K^2*q*D*2^(C*((q+q-1)/q)) ≤ D') :
    op869_bounded_adversary_forces 3 q K D' n' 0 (fun _ : Fin n' => ∅) (fun _ : Fin n' => ∅) := by
  let A := C*K^2*q*2^(C*((q+q-1)/q))
  have hC0 : 0 < C := by omega
  have hq0 : 0 < q := by omega
  have hK0 : 0 < K := by omega
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hA : 1 ≤ A := hA0
  have hn' : n ≤ n' := by
    calc
      n = n*1*1 := by simp
      _ ≤ n*A*D := Nat.mul_le_mul (Nat.mul_le_mul_left n hA) hD
      _ = C*K^2*q*n*D*2^(C*((q+q-1)/q)) := by dsimp [A]; ring
      _ ≤ n' := hn
  have hDD : D ≤ D' := by
    calc
      D = 1*D := by simp
      _ ≤ A*D := Nat.mul_le_mul_right D hA
      _ = C*K^2*q*D*2^(C*((q+q-1)/q)) := by dsimp [A]; ring
      _ ≤ D' := hD'
  have hp := op869_bounded_initial_vertex_mono hn' 3 q K D (by decide) hgame
  exact op869_bounded_adversary_forces_mono_degree 3 q K D D' hDD n' 0 _ _ hp
