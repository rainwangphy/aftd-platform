import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869PredecessorPostdegree
import AFTD.Kb.Tcs.Op869GraphFromPredecessors

/-!
# op869_bounded_adversary_one_vertex

Topic: online_algorithms   Node: 7b2f8f44ed71

Provenance: helper lemma. arXiv:2610.41516, Section 2.2, post-degree controlled adaptive t-fold coloring simulation.

When n and k are positive, an isolated vertex forces t colors in the bounded t-fold game in one move, for every post-degree bound D.
-/

theorem op869_bounded_adversary_one_vertex {n k t D : ℕ} (hn : 0 < n) (hk : 0 < k) :
    op869_bounded_adversary_forces k t t D 1 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) := by
  simp only [op869_bounded_adversary_forces, dif_pos hn]
  refine ⟨∅, by simp, ?_, ?_, ?_⟩
  · refine ⟨SimpleGraph.Coloring.mk (fun _ => ⟨0, hk⟩) ?_⟩
    intro a b hadj
    have hempty : Function.update (fun _ : Fin n => (∅ : Finset (Fin n))) ⟨0, hn⟩ ∅ =
        (fun _ => ∅) := by funext x; simp
    rw [hempty] at hadj
    simp [op869_graph_from_predecessors] at hadj
  · intro a
    have hempty : Function.update (fun _ : Fin n => (∅ : Finset (Fin n))) ⟨0, hn⟩ ∅ =
        (fun _ => ∅) := by funext x; simp
    rw [hempty]
    simp [op869_predecessor_postdegree]
  · intro c hc _
    left
    have hmem : (⟨0, hn⟩ : Fin n) ∈ Finset.univ.filter (fun a : Fin n => a.val ≤ 0) := by simp
    have hsub : c ⊆ (Finset.univ.filter (fun a : Fin n => a.val ≤ 0)).biUnion
        (Function.update (fun _ : Fin n => (∅ : Finset ℕ)) ⟨0, hn⟩ c) := by
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨⟨0, hn⟩, hmem, by simpa using hx⟩
    simpa [hc] using Finset.card_le_card hsub
