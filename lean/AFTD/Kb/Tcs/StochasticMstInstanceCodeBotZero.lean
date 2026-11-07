import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstInstanceCode
import AFTD.Kb.Tcs.NatSelfDelimitingCode

/-!
# stochastic_mst_instance_code_bot_zero

Topic: approximation   Node: 97ec804d77a6

Provenance: helper lemma. Sanity check of stochastic_mst_instance_code (OP-851 encoding).

The empty graph on zero vertices is encoded by the single bit false.
-/

theorem stochastic_mst_instance_code_bot_zero (p : (⊥ : SimpleGraph (Fin 0)).edgeSet → ℚ) :
    stochastic_mst_instance_code 0 ⊥ p = [false] := by
  simp [stochastic_mst_instance_code]
