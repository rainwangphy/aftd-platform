import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# retained_line_component_count_le_left_roots

Topic: algorithms   Node: 3bf98ca6d9ff

Provenance: helper lemma. OP-815: deterministic component-count bound needed for a uniform tail estimate.

For a simple graph on the first n linearly ordered vertices, the number of connected components is at most the number of vertices with no adjacent vertex to their left.
-/

theorem retained_line_component_count_le_left_roots {n : ℕ} (G : SimpleGraph (Fin n)) :
    Nat.card G.ConnectedComponent ≤
      {v : Fin n | ∀ w : Fin n, w < v → ¬ G.Adj v w}.ncard := by
  classical
  let S := {v : Fin n | ∀ w : Fin n, w < v → ¬ G.Adj v w}
  have surj : Function.Surjective (fun v : S => G.connectedComponentMk v.1) := by
    intro c
    let F := c.supp.toFinset
    have ne : F.Nonempty := by
      simpa [F] using c.nonempty_supp
    let v := F.min' ne
    have hv : v ∈ c.supp := by
      simpa [F, v] using F.min'_mem ne
    have root : v ∈ S := by
      intro w hw hadj
      have hwc : w ∈ c.supp := (c.mem_supp_congr_adj hadj).mp hv
      have hwF : w ∈ F := by simpa [F] using hwc
      have hmin : v ≤ w := F.min'_le w hwF
      exact (not_lt_of_ge hmin) hw
    exact ⟨⟨v, root⟩, hv⟩
  have hcard := Nat.card_le_card_of_surjective (fun v : S => G.connectedComponentMk v.1) surj
  change Nat.card G.ConnectedComponent ≤ Nat.card S
  exact hcard
