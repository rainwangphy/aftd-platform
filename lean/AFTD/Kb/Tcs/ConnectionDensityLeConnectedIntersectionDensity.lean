import AFTD.Prelude
import AFTD.Kb.Tcs.ConnectedIntersectionDensity
import AFTD.Kb.Tcs.IsGeneratingConnectionSet
import AFTD.Kb.Tcs.ConnectionDensity

/-!
# connection_density_le_connected_intersection_density

Topic: combinatorics   Node: 6c007775ab13

Provenance: helper lemma. sanity lemma for connected_intersection_density (arXiv:2611.26732, Definition 1.4)

For every finite group $G$ and every inverse-closed generating connection set $S$, the density of $S$ is at most the connected intersection density $\rho_{\mathrm{gen}}(G)$.
-/

theorem connection_density_le_connected_intersection_density (G : Type*) [Group G] [Fintype G] (S : Finset G) (hS : is_generating_connection_set G S) : connection_density G S ≤ connected_intersection_density G := by
  classical
  unfold connected_intersection_density
  have hmem : S ∈ (Finset.univ : Finset (Finset G)).filter (fun S => is_generating_connection_set G S) := by
    simp [hS]
  rw [dif_pos ⟨S, hmem⟩]
  convert Finset.le_sup' (connection_density G) hmem
