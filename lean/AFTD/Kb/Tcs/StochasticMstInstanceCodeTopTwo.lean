import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstInstanceCode
import AFTD.Kb.Tcs.NatSelfDelimitingCode

/-!
# stochastic_mst_instance_code_top_two

Topic: approximation   Node: e31dc94a350a

Provenance: helper lemma. Sanity check of stochastic_mst_instance_code (OP-851 encoding).

The single edge on two vertices with probability 1/2 is encoded as 1,1,0 (n = 2 in unary), 1 (the pair 0,1 is adjacent), 1,1,0 (numerator 1), 1,0,1,1,0 (denominator 2, bits 0,1).
-/

theorem stochastic_mst_instance_code_top_two :
    stochastic_mst_instance_code 2 ⊤ (fun _ => 1 / 2) =
      [true, true, false, true, true, true, false, true, false, true, true, false] := by
  decide +kernel
