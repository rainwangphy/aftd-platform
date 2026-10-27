import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopTwoWord
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopInverseTwoWord
import AFTD.Kb.Tcs.SimpleGraphIsHop
import AFTD.Kb.Tcs.SimpleGraphNormalizedHop

/-!
# simple_graph_normalized_word_to_hop_word

Topic: graphs   Node: fb0d6b37e280

Provenance: helper lemma. Routine word-metric/cycle-factor assembly for IN-262 / OP-543, using the verified baseline normalization. The remaining quadratic diameter theorem is conjectural; no diameter assumption is silently discharged and no research advance is claimed.

Every signed normalized word lifts to an actual hop word with exactly twice its length and the same product.
-/

theorem simple_graph_normalized_word_to_hop_word {V : Type*} (G : SimpleGraph V)
    (h₀ : Equiv.Perm V) (hh₀ : simple_graph_is_hop G h₀)
    (w : List (Equiv.Perm V))
    (hw : ∀ p ∈ w, simple_graph_normalized_hop G h₀ p ∨
      simple_graph_normalized_hop G h₀ p⁻¹) :
    ∃ u : List (Equiv.Perm V), (∀ h ∈ u, simple_graph_is_hop G h) ∧
      u.length = 2*w.length ∧ u.prod = w.prod := by
  induction' w with p t ih
  · refine ⟨[], by simp, by simp, by simp⟩
  · have hp : simple_graph_normalized_hop G h₀ p ∨ simple_graph_normalized_hop G h₀ p⁻¹ :=
      hw p List.mem_cons_self
    have ht : ∀ q ∈ t, simple_graph_normalized_hop G h₀ q ∨ simple_graph_normalized_hop G h₀ q⁻¹ :=
      fun q hq => hw q (List.mem_cons_of_mem p hq)
    obtain ⟨u_t, hu_t_hop, hu_t_len, hu_t_prod⟩ := ih ht
    have h_p : ∃ w_p : List (Equiv.Perm V), (∀ h ∈ w_p, simple_graph_is_hop G h) ∧
        w_p.length = 2 ∧ w_p.prod = p := by
      rcases hp with hpos | hneg
      · exact simple_graph_normalized_hop_two_word G h₀ p hh₀ hpos
      · obtain ⟨w_p, hw1, hw2, hw3⟩ := simple_graph_normalized_hop_inverse_two_word G h₀ p⁻¹ hh₀ hneg
        refine ⟨w_p, hw1, hw2, ?_⟩
        rw [hw3, inv_inv]
    obtain ⟨w_p, hw_p_hop, hw_p_len, hw_p_prod⟩ := h_p
    refine ⟨w_p ++ u_t, ?_, ?_, ?_⟩
    · intro h hh
      rw [List.mem_append] at hh
      rcases hh with hh | hh
      · exact hw_p_hop h hh
      · exact hu_t_hop h hh
    · rw [List.length_append, hw_p_len, hu_t_len, List.length_cons]
      omega
    · rw [List.prod_append, hw_p_prod, hu_t_prod, List.prod_cons]
