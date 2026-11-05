import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetTransversalNumberMono
import AFTD.Kb.Tcs.FinsetTransversalNumber
import AFTD.Kb.Tcs.SimpleGraphIsFort
import AFTD.Kb.Tcs.IsCompatibleCollection
import AFTD.Kb.Tcs.SimpleGraphFortTransversalNumber

/-!
# simple_graph_fort_transversal_number_le_all_forts_transversal_number

Topic: graphs   Node: 3904241ff3c8

Provenance: helper lemma. step towards op_979_csym_max_nullity_lt_fort_transversal_number

For any finite simple graph G, the fort transversal number T(G) is at most the transversal number of the family of all forts of G.
-/

/-- For any finite simple graph G, the fort transversal number T(G) is at most the transversal number of the family of all forts of G. -/
theorem simple_graph_fort_transversal_number_le_all_forts_transversal_number
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    simple_graph_fort_transversal_number G ≤
      finset_transversal_number (open Classical in (Finset.univ : Finset (Finset V)).filter (fun F => simple_graph_is_fort G ↑F)) := by
  classical
  unfold simple_graph_fort_transversal_number
  apply csSup_le
  · refine ⟨finset_transversal_number ∅, ∅, ?_, ?_, rfl⟩
    · intro F hF; simp at hF
    · intro C1 hC1; simp at hC1
  · rintro k ⟨C, hC_fort, hC_compat, rfl⟩
    apply finset_transversal_number_mono
    · intro F hF
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ F, hC_fort F hF⟩
    · intro S hS
      rw [Finset.mem_filter] at hS
      exact Finset.coe_nonempty.mp hS.2.1
