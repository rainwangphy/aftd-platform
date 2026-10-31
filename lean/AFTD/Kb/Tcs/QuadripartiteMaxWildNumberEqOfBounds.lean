import AFTD.Prelude
import AFTD.Kb.Tcs.QuadripartiteMaxWildNumber
import AFTD.Kb.Tcs.SimpleGraphWildNumber

/-!
# quadripartite_max_wild_number_eq_of_bounds

Topic: graphs   Node: 1a2b3864fd85

Provenance: helper lemma. step towards quadripartite_minimum_coloring_max_wild_number_eq

The maximum wild number equals 2n + 1 as soon as every proper 3n-edge-colouring of K_{n,n,n,n} has wild number at most 2n + 1 and some such colouring has wild number exactly 2n + 1.
-/

/-- The maximum wild number is 2n + 1 once the universal upper bound and one attaining colouring are available. -/
theorem quadripartite_max_wild_number_eq_of_bounds (n : ℕ)
    (hU : ∀ c : (SimpleGraph.completeEquipartiteGraph 4 n).lineGraph.Coloring (Fin (3 * n)),
      simple_graph_wild_number (SimpleGraph.completeEquipartiteGraph 4 n) c ≤ 2 * n + 1)
    (hE : ∃ c : (SimpleGraph.completeEquipartiteGraph 4 n).lineGraph.Coloring (Fin (3 * n)),
      simple_graph_wild_number (SimpleGraph.completeEquipartiteGraph 4 n) c = 2 * n + 1) :
    quadripartite_max_wild_number n = 2 * n + 1 := by
  classical
  unfold quadripartite_max_wild_number
  set S := {k : ℕ | ∃ c : (SimpleGraph.completeEquipartiteGraph 4 n).lineGraph.Coloring (Fin (3 * n)),
    simple_graph_wild_number (SimpleGraph.completeEquipartiteGraph 4 n) c = k}
  have hbd : ∃ N, ∀ a ∈ S, a ≤ N := by
    use 2 * n + 1
    rintro a ⟨c, rfl⟩
    exact hU c
  rw [Nat.sSup_def hbd]
  apply le_antisymm
  · apply Nat.find_min'
    rintro a ⟨c, rfl⟩
    exact hU c
  · obtain ⟨c, hc⟩ := hE
    have hmem : 2 * n + 1 ∈ S := ⟨c, hc⟩
    exact Nat.find_spec hbd (2 * n + 1) hmem
