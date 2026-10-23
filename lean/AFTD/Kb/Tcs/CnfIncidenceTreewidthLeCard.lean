import AFTD.Prelude
import AFTD.Kb.Tcs.CnfIncidenceTreewidth
import AFTD.Kb.Tcs.CnfVars
import AFTD.Kb.Tcs.HasTreeDecompositionSingleBag
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.CnfIncidenceGraph
import AFTD.Kb.Tcs.HasTreeDecompositionOfWidthLe
import AFTD.Kb.Tcs.GraphTreewidth

/-!
# cnf_incidence_treewidth_le_card

Topic: proof_complexity   Node: ce3fa37495e1

Provenance: helper lemma. step towards resolution_fpt_incidence_treewidth

Universal upper bound: the incidence treewidth of any CNF formula F is at most |vars(F)| + |F|.
-/

/-- The incidence treewidth of any CNF formula is bounded above by the sum of the number of variables and the number of clauses. -/
theorem cnf_incidence_treewidth_le_card (F : Finset (Finset (CnfLit ℕ))) : cnf_incidence_treewidth F ≤ (cnf_vars F).card + F.card := by
  unfold cnf_incidence_treewidth graph_treewidth
  have h := has_tree_decomposition_single_bag (cnf_incidence_graph F)
  have hcard : Fintype.card (↥(cnf_vars F) ⊕ ↥F) = (cnf_vars F).card + F.card := by simp
  rw [hcard] at h
  exact le_trans (Nat.sInf_le h) (Nat.sub_le _ _)
