import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Connb
import AFTD.Kb.GameTheoryEconomics.Poc8CloseSound
import AFTD.Kb.GameTheoryEconomics.IsConnectedVertexSet
import AFTD.Kb.GameTheoryEconomics.Poc8Graph

/-!
# poc8_connb_sound

Topic: fair_division   Node: 5e11661b4897

If the Boolean connectivity test accepts S, then S induces a connected subgraph of G.
-/

theorem poc8_connb_sound (S : Fin 8 → Bool) (h : poc8_connb S = true) :
    is_connected_vertex_set poc8_graph {x | S x = true} := by
  simp only [poc8_connb, List.any_eq_true, List.all_eq_true, List.mem_finRange, true_and,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', forall_const] at h
  obtain ⟨r, hr, hall⟩ := h
  have key : ∀ v : {x | S x = true},
      (poc8_graph.induce {x | S x = true}).Reachable ⟨r, hr⟩ v := by
    rintro ⟨v, hv⟩
    rcases hall v with h | h
    · simp only [Set.mem_ofPred_eq] at hv
      rw [hv] at h
      exact absurd h (by decide)
    · exact (poc8_close_sound S r hr 7 v h).2
  have : Nonempty {x | S x = true} := ⟨⟨r, hr⟩⟩
  exact ⟨fun a b => (key a).symm.trans (key b)⟩
