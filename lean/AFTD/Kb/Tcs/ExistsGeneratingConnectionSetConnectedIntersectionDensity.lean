import AFTD.Prelude
import AFTD.Kb.Tcs.ConnectedIntersectionDensity
import AFTD.Kb.Tcs.IsGeneratingConnectionSetUnivEraseOne
import AFTD.Kb.Tcs.ConnectionDensity
import AFTD.Kb.Tcs.IsGeneratingConnectionSet

/-!
# exists_generating_connection_set_connected_intersection_density

Topic: combinatorics   Node: af2a3fbb6013

Provenance: helper lemma. sanity lemma for connected_intersection_density (arXiv:2611.26732, Definition 1.4)

For every finite group $G$ the maximum defining $\rho_{\mathrm{gen}}(G)$ is attained: some inverse-closed generating connection set $S$ has density exactly $\rho_{\mathrm{gen}}(G)$.
-/

theorem exists_generating_connection_set_connected_intersection_density (G : Type*) [Group G] [Fintype G] : ∃ S : Finset G, is_generating_connection_set G S ∧ connection_density G S = connected_intersection_density G := by
  classical
  unfold connected_intersection_density
  have hne : ((Finset.univ : Finset (Finset G)).filter (fun S => is_generating_connection_set G S)).Nonempty :=
    ⟨Finset.univ.erase 1, by simp [is_generating_connection_set_univ_erase_one]⟩
  rw [dif_pos hne]
  obtain ⟨S, hS, hEq⟩ := Finset.exists_mem_eq_sup' hne (connection_density G)
  refine ⟨S, (Finset.mem_filter.mp hS).2, ?_⟩
  rw [hEq]
