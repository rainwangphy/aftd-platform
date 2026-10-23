import AFTD.Prelude
import AFTD.Kb.Tcs.CnfIncidenceTreewidth
import AFTD.Kb.Tcs.CnfIncidenceTreewidthLeCard
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.CnfVars

/-!
# cnf_incidence_treewidth_empty

Topic: proof_complexity   Node: a6ad601840b8

Provenance: helper lemma. step towards resolution_fpt_incidence_treewidth

The incidence treewidth of the empty formula is 0.
-/

/-- The incidence treewidth of the empty formula is zero. -/
theorem cnf_incidence_treewidth_empty : cnf_incidence_treewidth (∅ : Finset (Finset (CnfLit ℕ))) = 0 := by
  have h := cnf_incidence_treewidth_le_card (∅ : Finset (Finset (CnfLit ℕ)))
  simp [cnf_vars] at h
  omega
