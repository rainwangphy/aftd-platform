import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pmms3cVerify
import AFTD.Kb.GameTheoryEconomics.Pmms3cTreeGet
import AFTD.Kb.GameTheoryEconomics.Pmms3cCert

/-!
# pmms3c_check_001

Topic: fair_division   Node: 7d00cb7a39fb

Provenance: helper lemma. step towards pmms_chores_three_agents_may_not_exist (three-agent chores PMMS, left open by arXiv:2609.10493) (kernel-checked violation certificates over all 3^9 allocations)

Kernel check of the stored certificates for the 729 allocations that give chores 0, 1, 2 to agents 0, 0, 1.
-/

theorem pmms3c_check_001 : ∀ d e f g h k : Fin 3, pmms3c_verify ![0, 0, 1, d, e, f, g, h, k] (pmms3c_tree_get pmms3c_cert [0, 0, 1, d, e, f, g, h, k]) = true := by
  decide +kernel
