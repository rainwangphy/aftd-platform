import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionWidthDvdOfHeightPrimeChain
import AFTD.Kb.Tcs.MondrianPrimeFreeHeightEncoding
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_two_prime_area_width_dvd

Topic: combinatorics   Node: 770391a8546c

Provenance: helper lemma. For OP-280, arXiv:2610.19193, Section 1. Related work: arXiv:2007.09639, Theorem 4.1; HAL:hal-05729522v2, Lemma 2.3 (primitive cross sections and common-side descent). The periodic residue argument and the uniform two-prime common-area exclusion are developed here.

For a perfect admissible square partition with common area q^s*p^t and q dividing the square side, every tile width is divisible by q.
-/

theorem mondrian_two_prime_area_width_dvd (n p q s t : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hP : mondrian_is_partition n P) (hz : mondrian_defect P = 0) (hqn : q ∣ n)
    (harea : ∀ r ∈ P, mondrian_rect_area r = q ^ s * p ^ t) :
    ∀ r ∈ P, q ∣ mondrian_rect_width r := by
  apply mondrian_partition_width_dvd_of_height_prime_chain n q p (q ^ s) P hP hz hqn hp (pow_pos hq.pos s)
  intro r hr hqr
  exact mondrian_prime_free_height_encoding p q s t (mondrian_rect_width r) (mondrian_rect_height r)
    hp hq (harea r hr) hqr
