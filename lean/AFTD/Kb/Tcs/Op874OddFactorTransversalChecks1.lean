import AFTD.Prelude
import AFTD.Kb.Tcs.Op874OddFactorTransversalSlots

/-!
# op874_odd_factor_transversal_checks_1

Topic: graphs   Node: 0a8d557ac5a7

Provenance: helper lemma. Explicit three odd-cycle independent-transversal obstruction based on https://arxiv.org/html/2309.12150 section 2.2; experiment 35359.

Every encoded choice in block 1 of the finite transversal check contains a conflict.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Obstruction
theorem block_3 : ∀ c : Fin 243, bad (c.val + 729) = true := by decide
end In1081Obstruction
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Obstruction
theorem block_4 : ∀ c : Fin 243, bad (c.val + 972) = true := by decide
end In1081Obstruction
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Obstruction
theorem block_5 : ∀ c : Fin 243, bad (c.val + 1215) = true := by decide
end In1081Obstruction
open In1081Obstruction

theorem op874_odd_factor_transversal_checks_1 :
  (∀ c : Fin 243, bad (c.val + 729) = true) ∧
  (∀ c : Fin 243, bad (c.val + 972) = true) ∧
  (∀ c : Fin 243, bad (c.val + 1215) = true) := by
  exact ⟨block_3, block_4, block_5⟩
