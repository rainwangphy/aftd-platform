import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.IsExtremalPerm
import AFTD.Kb.NumberTheory.GoodSlopesGapThreeCoprimeFromFiberBounds
import AFTD.Kb.NumberTheory.GoodSlopesFiber55UnitGap
import AFTD.Kb.NumberTheory.GoodSlopesUnitCoverSquarefree
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesFiber55NonunitCollisionGap

/-!
# good_slopes_gap_mod_165_le_76

Topic: elementary_number_theory   Node: c2d782e7b0c7

Provenance: original. Related work: The open gap question and modulus-165 case are in https://arxiv.org/abs/2611.04551, Question 10.2 and Table 3.

Every non-extremal permutation of the integers modulo 165 has at most 76 good slopes.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
private theorem in962_gap76_squarefree : Squarefree 165 := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have h : Squarefree ((3*5)*11 : ℕ) :=
    (Nat.squarefree_mul (by norm_num)).2
      ⟨(Nat.squarefree_mul (by norm_num)).2 ⟨hp3.squarefree, hp5.squarefree⟩,
       hp11.squarefree⟩
  exact h

theorem good_slopes_gap_mod_165_le_76 (f : Equiv.Perm (ZMod 165)) (hf : ¬ is_extremal_perm 165 f) : (good_slopes 165 f).card ≤ 76 := by
  obtain ⟨c, _, hc⟩ := good_slopes_unit_cover_squarefree 165 in962_gap76_squarefree f
  have h := good_slopes_gap_three_coprime_from_fiber_bounds 55 40 2 (by decide) f hf
    ⟨c,hc⟩ good_slopes_fiber55_nonunit_collision_gap_card_units (by decide) (by decide)
    (by
      intro S hs hb
      have hg := good_slopes_fiber55_unit_gap S hs hb
      omega)
    (by
      intro S color hs hx hc hb
      have hg := good_slopes_fiber55_unit_gap S hs hb
      omega)
  exact h
