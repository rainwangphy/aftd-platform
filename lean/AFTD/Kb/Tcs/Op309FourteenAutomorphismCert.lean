import AFTD.Prelude
import AFTD.Kb.Tcs.Op309FourteenIncidence

/-!
# op309_fourteen_automorphism_cert

Topic: graphs   Node: 82d790073b35

Provenance: helper lemma. Finite incidence certificate for the fourteen-vertex OP-309 palette obstruction, experiments 34668, 34677, 34678.

Every listed matching has a verified side-preserving symmetry from the canonical matching.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem op309_fourteen_automorphism_cert : ∀ k : Fin 24,
    Function.Injective (op309_fourteen_alpha k) ∧ Function.Injective (op309_fourteen_beta k) ∧
    (∀ i j : Fin 7, (∃ t : Fin 3, op309_fourteen_incidence i t = j) ↔
      (∃ t : Fin 3, op309_fourteen_incidence (op309_fourteen_alpha k i) t = op309_fourteen_beta k j)) ∧
    (∀ i : Fin 7, op309_fourteen_beta k (op309_fourteen_base i) =
      op309_fourteen_incidence (op309_fourteen_alpha k i) (op309_fourteen_matchings k (op309_fourteen_alpha k i))) := by
  decide
