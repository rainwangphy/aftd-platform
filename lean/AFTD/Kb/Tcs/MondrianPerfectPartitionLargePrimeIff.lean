import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianLargePrimeDescent
import AFTD.Kb.Tcs.MondrianPerfectPartitionMul
import AFTD.Kb.Tcs.MondrianRectMul

/-!
# mondrian_perfect_partition_large_prime_iff

Topic: combinatorics   Node: c2108bff7661

Provenance: original. Related work: OP-280, arXiv:2610.19193, Section 1, asks whether any perfect partition exists and notes scaling. arXiv:2007.09639, Theorem 4.1, gives prime-power and fixed-exponent exclusions. The uniform p>c prime-removal equivalence is proved here.

For every positive integer c, prime p greater than c, and natural exponent e, the square of side c times p to the e has a perfect admissible integer-rectangle partition if and only if the c-square has one.
-/

theorem mondrian_perfect_partition_large_prime_iff (c p e : ℕ) (hc : 0 < c)
    (hp : Nat.Prime p) (hpc : c < p) :
    (∃ P, mondrian_is_partition (c * p ^ e) P ∧ mondrian_defect P = 0) ↔
      ∃ Q, mondrian_is_partition c Q ∧ mondrian_defect Q = 0 := by
  constructor
  · exact mondrian_large_prime_descent c p e hc hp hpc
  · rintro ⟨Q, hQ, hz⟩
    refine ⟨Q.map (mondrian_rect_mul (p ^ e)), ?_⟩
    simpa only [Nat.mul_comm] using
      mondrian_perfect_partition_mul (p ^ e) c (pow_pos hp.pos e) Q hQ hz
