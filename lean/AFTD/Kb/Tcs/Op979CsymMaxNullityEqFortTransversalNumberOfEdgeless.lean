import AFTD.Prelude
import AFTD.Kb.Tcs.Op979CsymMaxNullityEmptyGraph
import AFTD.Kb.Tcs.Op979FortTransversalNumberEmptyGraph
import AFTD.Kb.Tcs.SimpleGraphFortTransversalNumber
import AFTD.Kb.Tcs.SimpleGraphCsymMaxNullity

/-!
# op_979_csym_max_nullity_eq_fort_transversal_number_of_edgeless

Topic: graphs   Node: a22ace761321

Provenance: formalization of a published result. Source: arXiv:2611.01102 Sec. 5 and Sec. 6

For the edgeless graph bot on a finite vertex set V with decidable equality, the combinatorially symmetric maximum nullity equals the fort transversal number.
-/

/-- For the edgeless graph on a finite vertex set V, N(⊥) = T(⊥). -/
theorem op_979_csym_max_nullity_eq_fort_transversal_number_of_edgeless
    {V : Type*} [Fintype V] [DecidableEq V] :
    simple_graph_csym_max_nullity (⊥ : SimpleGraph V) =
      simple_graph_fort_transversal_number (⊥ : SimpleGraph V) := by
  rw [op_979_csym_max_nullity_empty_graph, op_979_fort_transversal_number_empty_graph]
