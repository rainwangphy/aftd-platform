import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.GoodSlopesMissingPrime165
import AFTD.Kb.NumberTheory.GoodSlopesUnitCoverSquarefree

/-!
# good_slopes_unit_cover_mod165

Topic: elementary_number_theory   Node: bba89135b73a

Provenance: helper lemma. The modulus-165 instance of arXiv:2611.01465, Theorem 3.1(i), for OP-1027.

For every permutation modulo 165, a unit c exists such that adding c to each good slope yields a unit modulo 165.
-/

private theorem in962_cover_squarefree165 : Squarefree 165 := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have h : Squarefree ((3*5)*11 : ℕ) :=
    (Nat.squarefree_mul (by norm_num)).2
      ⟨(Nat.squarefree_mul (by norm_num)).2 ⟨hp3.squarefree, hp5.squarefree⟩,
       hp11.squarefree⟩
  exact h

theorem good_slopes_unit_cover_mod165 (f : Equiv.Perm (ZMod 165)) : ∃ c : ZMod 165, IsUnit c ∧ ∀ m ∈ good_slopes 165 f, IsUnit (m+c) := by
  exact good_slopes_unit_cover_squarefree 165 in962_cover_squarefree165 f
