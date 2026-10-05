import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Discb
import AFTD.Kb.GameTheoryEconomics.Poc8CutbSound
import AFTD.Kb.GameTheoryEconomics.IsConnectedVertexSet
import AFTD.Kb.GameTheoryEconomics.Poc8Graph

/-!
# poc8_discb_sound

Topic: fair_division   Node: b85506f29643

If the Boolean disconnectedness test accepts S, then S does not induce a connected subgraph of G.
-/

theorem poc8_discb_sound (S : Fin 8 → Bool) (h : poc8_discb S = true) :
    ¬ is_connected_vertex_set poc8_graph {x | S x = true} := by
  simp only [poc8_discb, Bool.or_eq_true, List.all_eq_true, List.any_eq_true, List.mem_finRange,
    true_and, Bool.and_eq_true, Bool.not_eq_true', forall_const] at h
  rcases h with h | ⟨r, _, hcut⟩
  · intro hc
    obtain ⟨⟨v, hv⟩⟩ := hc.nonempty
    simp only [Set.mem_ofPred_eq] at hv
    rw [h v] at hv
    exact absurd hv (by decide)
  · exact poc8_cutb_sound S _ hcut
