import AFTD.Prelude
import AFTD.Kb.Tcs.Multigraph
import AFTD.Kb.Tcs.MultigraphChromaticIndex
import AFTD.Kb.Tcs.MultigraphLocalChromaticIndex
import AFTD.Kb.Tcs.MultigraphIsProperEdgeColoring
import AFTD.Kb.Tcs.MultigraphIsLocallyBounded

/-!
# multigraph_chromatic_index_le_local_chromatic_index

Topic: graphs   Node: f696ecf445d7

Provenance: formalization of a published result. Source: scout/2611-29111-when-do-local-bounds-permit-optimal-edge-colorings.md:76

For any multigraph G on a finite vertex type V admitting a locally bounded proper edge-coloring, its chromatic index is at most its local chromatic index: chi'(G) <= chi'_loc(G).
-/

/-- The ordinary chromatic index of a multigraph is at most its local chromatic index. -/
theorem multigraph_chromatic_index_le_local_chromatic_index {V : Type*} [Fintype V] (G : Multigraph V) (h : ∃ k, ∃ c : V → V → Finset ℕ, multigraph_is_proper_edge_coloring G k c ∧ multigraph_is_locally_bounded G c) : multigraph_chromatic_index G ≤ multigraph_local_chromatic_index G := by
  unfold multigraph_chromatic_index multigraph_local_chromatic_index
  obtain ⟨k, c, hc, hb⟩ := h
  have hS : ({k | ∃ c, multigraph_is_proper_edge_coloring G k c ∧ multigraph_is_locally_bounded G c} : Set ℕ).Nonempty :=
    ⟨k, c, hc, hb⟩
  have hmem := Nat.sInf_mem hS
  apply Nat.sInf_le
  obtain ⟨c', hc', -⟩ := hmem
  exact ⟨c', hc'⟩
