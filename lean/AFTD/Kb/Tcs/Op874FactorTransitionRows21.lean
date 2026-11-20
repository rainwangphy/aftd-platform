import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_21

Topic: graphs   Node: 11efe648ac7d

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 21 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_84 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[84]!).testBit j.val = decide (wordStep d.val (wordStates[84]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_85 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[85]!).testBit j.val = decide (wordStep d.val (wordStates[85]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_86 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[86]!).testBit j.val = decide (wordStep d.val (wordStates[86]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_87 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[87]!).testBit j.val = decide (wordStep d.val (wordStates[87]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_21 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[84]!).testBit j.val = decide (wordStep d.val (wordStates[84]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[85]!).testBit j.val = decide (wordStep d.val (wordStates[85]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[86]!).testBit j.val = decide (wordStep d.val (wordStates[86]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[87]!).testBit j.val = decide (wordStep d.val (wordStates[87]!) (wordStates[j.val]!))) := by
  exact ⟨row_84 d j, row_85 d j, row_86 d j, row_87 d j⟩
