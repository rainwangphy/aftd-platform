import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8LinkedTwoThree
import AFTD.Kb.GameTheoryEconomics.Poc8NotLinkedTwoFour
import AFTD.Kb.GameTheoryEconomics.Poc8GmmsCheck
import AFTD.Kb.GameTheoryEconomics.Poc8GmmsOk
import AFTD.Kb.GameTheoryEconomics.Poc8ValEq
import AFTD.Kb.GameTheoryEconomics.Poc8DiscbSound
import AFTD.Kb.GameTheoryEconomics.Poc8U
import AFTD.Kb.GameTheoryEconomics.IsAbLinked
import AFTD.Kb.GameTheoryEconomics.IsConnectedVertexSet
import AFTD.Kb.GameTheoryEconomics.Poc8Graph
import AFTD.Kb.GameTheoryEconomics.Poc8Val

/-!
# poc_linkedness_conjecture_counterexample

Topic: fair_division   Node: 47cebf431911

Counterexample to arXiv:1908.05433 Conjecture 3.10 for two agents: there is a graph G on 8 vertices that is (2,3)-linked but not (2,4)-linked, so the conjecture (with k = 4) predicts PoC(G,2) = 8/7, yet with u = (5,5,5,1,1,1,12,0) the maximin share is 15 (split {0,1,2,7} versus the rest) while every bipartition of G into two connected parts gives the poorer part at most 13. Hence PoC(G,2) ≥ 15/13 > 8/7.
-/

theorem poc_linkedness_conjecture_counterexample :
    ∃ G : SimpleGraph (Fin 8), is_ab_linked G 2 3 ∧ ¬ is_ab_linked G 2 4 ∧
      ∃ u : Fin 8 → ℝ, (∀ v, 0 ≤ u v) ∧ ∃ S : Finset (Fin 8), ∀ T : Finset (Fin 8),
        is_connected_vertex_set G (↑T : Set (Fin 8)) →
        is_connected_vertex_set G (↑(Tᶜ) : Set (Fin 8)) →
          8 * min (∑ v ∈ T, u v) (∑ v ∈ Tᶜ, u v) < 7 * min (∑ v ∈ S, u v) (∑ v ∈ Sᶜ, u v) := by
  refine ⟨poc8_graph, poc8_linked_two_three, poc8_not_linked_two_four, fun v => (poc8_u v : ℝ),
    fun v => Nat.cast_nonneg _, {0, 1, 2, 7}, fun T hT hTc => ?_⟩
  have hok := poc8_gmms_check (fun v => decide (v ∈ T))
  simp only [poc8_gmms_ok, Bool.or_eq_true, decide_eq_true_eq] at hok
  have eT : {x | decide (x ∈ T) = true} = (↑T : Set (Fin 8)) := by ext; simp
  have eTc : {x | (!decide (x ∈ T)) = true} = (↑(Tᶜ) : Set (Fin 8)) := by ext; simp
  rcases hok with (h | h) | h
  · have fT : Finset.univ.filter (fun v => decide (v ∈ T) = true) = T := by ext; simp
    have fTc : Finset.univ.filter (fun v => (!decide (v ∈ T)) = true) = Tᶜ := by ext; simp
    have vT := poc8_val_eq (fun v => decide (v ∈ T))
    have vTc := poc8_val_eq (fun v => !decide (v ∈ T))
    rw [fT] at vT
    rw [fTc] at vTc
    have nS : poc8_val (fun v => decide (v ∈ ({0, 1, 2, 7} : Finset (Fin 8)))) = 15 := by decide
    have nSc : poc8_val (fun v => !decide (v ∈ ({0, 1, 2, 7} : Finset (Fin 8)))) = 15 := by decide
    have vS := poc8_val_eq (fun v => decide (v ∈ ({0, 1, 2, 7} : Finset (Fin 8))))
    have vSc := poc8_val_eq (fun v => !decide (v ∈ ({0, 1, 2, 7} : Finset (Fin 8))))
    have fS : Finset.univ.filter (fun v => decide (v ∈ ({0, 1, 2, 7} : Finset (Fin 8))) = true) =
        {0, 1, 2, 7} := by ext; simp
    have fSc : Finset.univ.filter
        (fun v => (!decide (v ∈ ({0, 1, 2, 7} : Finset (Fin 8)))) = true) =
        ({0, 1, 2, 7} : Finset (Fin 8))ᶜ := by ext; simp
    rw [fS, nS] at vS
    rw [fSc, nSc] at vSc
    rw [← vT, ← vTc, ← vS, ← vSc]
    have h' : ((8 * min (poc8_val fun v => decide (v ∈ T)) (poc8_val fun v => !decide (v ∈ T)) : ℕ)
        : ℝ) < 105 := by exact_mod_cast h
    push_cast at h'
    norm_num
    linarith
  · exact absurd hT (by rw [← eT]; exact poc8_discb_sound _ h)
  · exact absurd hTc (by rw [← eTc]; exact poc8_discb_sound _ h)
