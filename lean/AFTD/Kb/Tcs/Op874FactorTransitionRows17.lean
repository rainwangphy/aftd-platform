import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_17

Topic: graphs   Node: 5f8877b5aca7

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 17 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_68 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[68]!).testBit j.val = decide (wordStep d.val (wordStates[68]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_69 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[69]!).testBit j.val = decide (wordStep d.val (wordStates[69]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_70 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[70]!).testBit j.val = decide (wordStep d.val (wordStates[70]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_71 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[71]!).testBit j.val = decide (wordStep d.val (wordStates[71]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_17 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[68]!).testBit j.val = decide (wordStep d.val (wordStates[68]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[69]!).testBit j.val = decide (wordStep d.val (wordStates[69]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[70]!).testBit j.val = decide (wordStep d.val (wordStates[70]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[71]!).testBit j.val = decide (wordStep d.val (wordStates[71]!) (wordStates[j.val]!))) := by
  exact ⟨row_68 d j, row_69 d j, row_70 d j, row_71 d j⟩
