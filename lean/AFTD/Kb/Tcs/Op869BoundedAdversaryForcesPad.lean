import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869BoundedVertexPadding
import AFTD.Kb.Tcs.Op869ExtendPredecessors
import AFTD.Kb.Tcs.Op869ExtendColors

/-!
# op869_bounded_adversary_forces_pad

Topic: online_algorithms   Node: a481c27a685c

Provenance: helper lemma. step towards op869_online_coloring_deterministic_lower_bound

A winning position on Fin n stays winning on Fin (n+m) when the extra vertices are added as isolated vertices with empty predecessor and colour sets.
-/

/-- Padding a winning bounded-adversary position by isolated vertices gives a winning position on the larger vertex set. -/
theorem op869_bounded_adversary_forces_pad {n m : ℕ} (k t K D : ℕ) (hk : 1 ≤ k)
    (fuel i : ℕ) (P : Fin n → Finset (Fin n)) (C : Fin n → Finset ℕ)
    (h : op869_bounded_adversary_forces k t K D fuel i P C) :
    op869_bounded_adversary_forces k t K D fuel i
      (fun j : Fin (n + m) => if hj : (j : ℕ) < n then (P ⟨j, hj⟩).image (Fin.castLE (Nat.le_add_right n m)) else ∅)
      (fun j : Fin (n + m) => if hj : (j : ℕ) < n then C ⟨j, hj⟩ else ∅) := by
  have hp := op869_bounded_vertex_padding (Nat.le_add_right n m) k t K D hk fuel i P C h
  have hpred : op869_extend_predecessors (Nat.le_add_right n m) P =
      (fun j : Fin (n + m) => if hj : (j : ℕ) < n then (P ⟨j, hj⟩).image (Fin.castLE (Nat.le_add_right n m)) else ∅) := by
    funext j
    simp [op869_extend_predecessors, Finset.map_eq_image]
  exact hpred ▸ hp
