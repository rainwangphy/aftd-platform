import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_19

Topic: graphs   Node: da49d06a385d

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 19 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_76 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[76]!).testBit j.val = decide (wordStep d.val (wordStates[76]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_77 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[77]!).testBit j.val = decide (wordStep d.val (wordStates[77]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_78 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[78]!).testBit j.val = decide (wordStep d.val (wordStates[78]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_79 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[79]!).testBit j.val = decide (wordStep d.val (wordStates[79]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_19 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[76]!).testBit j.val = decide (wordStep d.val (wordStates[76]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[77]!).testBit j.val = decide (wordStep d.val (wordStates[77]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[78]!).testBit j.val = decide (wordStep d.val (wordStates[78]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[79]!).testBit j.val = decide (wordStep d.val (wordStates[79]!) (wordStates[j.val]!))) := by
  exact ⟨row_76 d j, row_77 d j, row_78 d j, row_79 d j⟩
