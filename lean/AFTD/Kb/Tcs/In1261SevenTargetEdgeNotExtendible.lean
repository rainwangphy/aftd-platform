import AFTD.Prelude
import AFTD.Kb.Tcs.In1261SevenGraph
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.IndexedDisjointCrossEdgesFormMatching
import AFTD.Kb.Tcs.OddGroupsBudgetAfterForcedMatching
import AFTD.Kb.Tcs.In1261SevenForbiddenOrdered
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.F

/-!
# in1261_seven_target_edge_not_extendible

Topic: graphs   Node: 583399dee129

Provenance: helper lemma. OP-1957: finite seven-by-seven control from experiment 43349; related problem arXiv:2611.22690.

Deleting the edge from vertex 0 to vertex 14 leaves the explicit seven-by-seven control graph not 7-extendible.
-/

set_option maxHeartbeats 4000000
set_option linter.all false
local instance  aftdLocal_e6441a87442aa8c3_0 : DecidableRel in1261_seven_graph.Adj := by
  unfold in1261_seven_graph in1261_seven_forbidden_ordered
  infer_instance
private theorem in1261_free_test :
  let f : Fin 7 → Fin 28 := ![5,15,17,19,22,24,26]
  let g : Fin 7 → Fin 28 := ![6,16,18,20,23,25,27]
  let F : Fin 3 → Finset (Fin 28) := ![{0},{1,2,3},{7,8,9,10,11,12,13,14,21}]
  ∀ i : Fin 3, ∀ u : Fin 28, u ∈ F i →
    (∀ t : Fin 7, f t ≠ u) ∧ (∀ t : Fin 7, g t ≠ u) := by
  decide

theorem in1261_seven_target_edge_not_extendible:
    ¬ is_k_extendable (in1261_seven_graph.deleteEdges {s((0 : Fin 28),(14 : Fin 28))}) 7 := by
  classical
  intro hExt
  let H := in1261_seven_graph.deleteEdges {s((0 : Fin 28),(14 : Fin 28))}
  let f : Fin 7 → Fin 28 := ![5,15,17,19,22,24,26]
  let g : Fin 7 → Fin 28 := ![6,16,18,20,23,25,27]
  have hf : Function.Injective f := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [f]
  have hg : Function.Injective g := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [g]
  have hfg : ∀ i j, f i ≠ g j := by intro i j; fin_cases i <;> fin_cases j <;> decide
  have hadj : ∀ i, H.Adj (f i) (g i) := by intro i; fin_cases i <;> decide
  obtain ⟨M,hM,hMcard,hMverts⟩ := indexed_disjoint_cross_edges_form_matching H 7 f g hf hg hfg hadj
  obtain ⟨P,hP,hMP⟩ := hExt.2.2 M hM hMcard
  let F : Fin 3 → Finset (Fin 28) := ![{0},{1,2,3},{7,8,9,10,11,12,13,14,21}]
  let L : Finset (Fin 28) := {0,1,2,3,7,8,9,10,11,12,13,14,21}
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin 3)), F i ⊆ L := by
    intro i hi; fin_cases i <;> decide
  have hodd : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Odd (F i).card := by
    intro i hi; fin_cases i <;> decide
  have hdis : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∀ j ∈ (Finset.univ : Finset (Fin 3)), i ≠ j → Disjoint (F i) (F j) := by
    intro i hi j hj hij; fin_cases i <;> fin_cases j <;> simp_all [F] <;> decide
  have hanti : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∀ u ∈ F i, ∀ v ∈ L, v ∉ F i → ¬ H.Adj u v := by
    intro i hi; fin_cases i <;> decide
  have hfree0 : ∀ i : Fin 3, ∀ u : Fin 28, u ∈ F i →
      (∀ t : Fin 7, f t ≠ u) ∧ (∀ t : Fin 7, g t ≠ u) := by
    simpa only [F,f,g] using in1261_free_test
  have hfree : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∀ u ∈ F i, u ∉ M.verts := by
    intro i hi u hu
    rw [hMverts]
    simp only [Set.mem_union, Set.mem_range, not_or, not_exists]
    exact hfree0 i u hu
  have hb := odd_groups_budget_after_forced_matching H P M hP hM hMP Finset.univ F L hsub hodd hdis hanti hfree
  have hcard : ((Finset.univ \ L).filter (fun v => v ∉ M.verts)).card=1 := by
    simp only [hMverts]
    decide
  rw [hcard] at hb
  simp at hb
