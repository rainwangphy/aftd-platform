import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPairBlocked

/-!
# efx_pair_blocked_witness

Topic: fair_division   Node: 7ab64a6044c0

Provenance: helper lemma. step towards efx_allsource_equal_pairs_ir_completion

The blocking predicate is satisfiable: if an agent values the charity good at 2 and every old good at 1, she blocks every old pair she does not own.
-/

/-- The blocking predicate is inhabited: an agent who values charity at 2 and old goods at 1 blocks a foreign pair. -/
theorem efx_pair_blocked_witness :
  efx_pair_blocked (fun (_ : Fin 4) (g : Fin 9) => if g = 8 then (2 : ℝ) else 1) 0 1 := by
  dsimp [efx_pair_blocked]
  norm_num
