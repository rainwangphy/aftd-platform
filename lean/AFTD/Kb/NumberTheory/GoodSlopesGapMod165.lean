import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.IsExtremalPerm
import AFTD.Kb.NumberTheory.GoodSlopesGapThreeCoprimeFromFiberBounds
import AFTD.Kb.NumberTheory.GoodSlopesUnitCoverMod165
import AFTD.Kb.NumberTheory.GoodSlopesFiber55UnitGap
import AFTD.Kb.NumberTheory.GoodSlopesFiber55ColoredGapStructural
import AFTD.Kb.NumberTheory.GoodSlopesFiber55NonunitCollisionGap
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections

/-!
# good_slopes_gap_mod_165

Topic: elementary_number_theory   Node: 52618ffcf34e

Provenance: original. Related work: arXiv:2611.04551 Question 10.2, the unsettled modulus 165.

Every non-extremal permutation of the residue ring modulo 165 has at most 72 good slopes.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_gap_mod_165 (f : Equiv.Perm (ZMod 165)) (hf : ¬ is_extremal_perm 165 f) : (good_slopes 165 f).card ≤ 72 := by
  obtain ⟨c, _, hc⟩ := good_slopes_unit_cover_mod165 f
  have h := good_slopes_gap_three_coprime_from_fiber_bounds 55 40 4 (by decide) f hf
    ⟨c,hc⟩ good_slopes_fiber55_nonunit_collision_gap_card_units (by decide) (by decide)
    (by
      intro S hs hb
      exact good_slopes_fiber55_unit_gap S hs hb)
    (by
      intro S color hs hx hc hb
      exact good_slopes_fiber55_colored_gap_structural S color hs hx hc hb)
  exact h
