import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pmms3cVerify
import AFTD.Kb.GameTheoryEconomics.Pmms3cTreeGet
import AFTD.Kb.GameTheoryEconomics.Pmms3cCert

/-!
# pmms3c_check_202

Topic: fair_division   Node: 98b2e564b5ac

Kernel check of the stored certificates for the 729 allocations that give chores 0, 1, 2 to agents 2, 0, 2.
-/

theorem pmms3c_check_202 : ∀ d e f g h k : Fin 3, pmms3c_verify ![2, 0, 2, d, e, f, g, h, k] (pmms3c_tree_get pmms3c_cert [2, 0, 2, d, e, f, g, h, k]) = true := by
  decide +kernel
