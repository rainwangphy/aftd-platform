import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Cutb
import AFTD.Kb.GameTheoryEconomics.Poc8NotConnectedOfCut
import AFTD.Kb.GameTheoryEconomics.Poc8Graph
import AFTD.Kb.GameTheoryEconomics.IsConnectedVertexSet
import AFTD.Kb.GameTheoryEconomics.Poc8Adj

/-!
# poc8_cutb_sound

Topic: fair_division   Node: 31694cf6859a

If the Boolean cut test accepts (S, R), then S does not induce a connected subgraph of G.
-/

theorem poc8_cutb_sound (S R : Fin 8 → Bool) (h : poc8_cutb S R = true) :
    ¬ is_connected_vertex_set poc8_graph {x | S x = true} := by
  simp only [poc8_cutb, List.any_eq_true, List.all_eq_true, List.mem_finRange, true_and,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', forall_const] at h
  obtain ⟨⟨⟨⟨a, ha⟩, hRS⟩, ⟨b, hbS, hbR⟩⟩, hcl⟩ := h
  refine poc8_not_connected_of_cut poc8_graph {x | S x = true} {x | R x = true} a b ?_ ha hbS
    (by simp [hbR]) ?_
  · rcases hRS a with h | h
    · rw [ha] at h; exact absurd h (by decide)
    · exact h
  · intro v w hv hw hadj
    simp only [Set.mem_ofPred_eq] at hv hw ⊢
    have hadj' : poc8_adj w v = true := hadj
    rcases hcl v w with ((h | h) | h) | h
    · rw [hv] at h; exact absurd h (by decide)
    · rw [hw] at h; exact absurd h (by decide)
    · rw [hadj'] at h; exact absurd h (by decide)
    · exact h
