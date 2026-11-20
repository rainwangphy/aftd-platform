import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_18

Topic: graphs   Node: 6fce3f06449c

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 18 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_72 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[72]!).testBit j.val = decide (wordStep d.val (wordStates[72]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_73 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[73]!).testBit j.val = decide (wordStep d.val (wordStates[73]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_74 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[74]!).testBit j.val = decide (wordStep d.val (wordStates[74]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_75 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[75]!).testBit j.val = decide (wordStep d.val (wordStates[75]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_18 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[72]!).testBit j.val = decide (wordStep d.val (wordStates[72]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[73]!).testBit j.val = decide (wordStep d.val (wordStates[73]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[74]!).testBit j.val = decide (wordStep d.val (wordStates[74]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[75]!).testBit j.val = decide (wordStep d.val (wordStates[75]!) (wordStates[j.val]!))) := by
  exact ⟨row_72 d j, row_73 d j, row_74 d j, row_75 d j⟩
