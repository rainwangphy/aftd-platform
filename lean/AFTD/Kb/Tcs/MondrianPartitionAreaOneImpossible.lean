import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_partition_area_one_impossible

Topic: combinatorics   Node: d5fd9a0daa4c

Provenance: helper lemma. For OP-280, arXiv:2610.19193, Section 1. Related work: arXiv:2007.09639, Theorem 4.1; HAL:hal-05729522v2, Lemma 2.3 (primitive cross sections and common-side descent). The periodic residue argument and the uniform two-prime common-area exclusion are developed here.

An admissible square partition cannot have every tile of area one.
-/

theorem mondrian_partition_area_one_impossible (n : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (hP : mondrian_is_partition n P) (harea : ∀ r ∈ P, mondrian_rect_area r = 1) : False := by
  cases P with
  | nil => have := hP.1; simp at this
  | cons r P =>
    cases P with
    | nil => have := hP.1; simp at this
    | cons s P =>
      have hrw := Nat.eq_one_of_mul_eq_one_right (harea r (by simp))
      have hrh := Nat.eq_one_of_mul_eq_one_left (harea r (by simp))
      have hsw := Nat.eq_one_of_mul_eq_one_right (harea s (by simp))
      have hsh := Nat.eq_one_of_mul_eq_one_left (harea s (by simp))
      have hpair := (List.pairwise_cons.mp hP.2.2.1).1 s (by simp)
      exact hpair.2 (Or.inl ⟨by omega, by omega⟩)
