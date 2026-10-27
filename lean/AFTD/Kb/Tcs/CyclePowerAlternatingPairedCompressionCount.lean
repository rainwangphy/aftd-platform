import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerSumRangeDouble

/-!
# cycle_power_alternating_paired_compression_count

Topic: combinatorics   Node: d8b77bf4f2a6

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635, Section 3. These conditional class-system and pruning lemmas do not establish the unresolved graph covering bound. The earlier fixed-radius helpers handle radii eight and sixteen; this session works with arbitrary dyadic radii. No research advance is claimed.

At every odd vertex, when all even-start classes consist exactly of their two endpoints, the original active count is one plus the count after retaining odd-start classes and halving the even ages. This identity does not need the consecutive-bit-pairing assumption.
-/

open Finset

theorem cycle_power_alternating_paired_compression_count
    (h : ℕ) (hh : 0 < h) (x : ℤ → ℕ → Bool)
    (heven : ∀ p : ℤ, ∀ j < 2 * h,
      x (2 * p) j = true ↔ j = 0 ∨ j = 2 * h - 1) :
    ∀ u : ℤ,
    (range (2 * h)).sum (fun j => (x (2 * u + 1 - (j : ℤ)) j).toNat) =
      1 + (range h).sum (fun j => (x (2 * (u - (j : ℤ)) + 1) (2 * j)).toNat) := by
  intro u
  rw [cycle_power_sum_range_double, sum_add_distrib]
  have hleft :
      (range h).sum (fun j => (x (2 * u + 1 - ((2 * j : ℕ) : ℤ)) (2 * j)).toNat) =
      (range h).sum (fun j => (x (2 * (u - (j : ℤ)) + 1) (2 * j)).toNat) := by
    apply sum_congr rfl
    intro j hj
    congr 2
    push_cast
    ring
  rw [hleft]
  have hodd :
      (range h).sum (fun j => (x (2 * u + 1 - ((2 * j + 1 : ℕ) : ℤ)) (2 * j + 1)).toNat) = 1 := by
    rw [sum_eq_single (h - 1)]
    · have he : 2 * u + 1 - ((2 * (h - 1) + 1 : ℕ) : ℤ) =
          2 * (u - ((h - 1 : ℕ) : ℤ)) := by push_cast; ring
      have hi : 2 * (h - 1) + 1 < 2 * h := by omega
      rw [he, (heven _ _ hi).mpr (Or.inr (by omega))]
      rfl
    · intro j hj hne
      have hi : j < h := mem_range.mp hj
      have he : 2 * u + 1 - ((2 * j + 1 : ℕ) : ℤ) = 2 * (u - (j : ℤ)) := by
        push_cast; ring
      rw [he]
      have hfalse : x (2 * (u - (j : ℤ))) (2 * j + 1) = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        have := (heven _ _ (by omega)).mp ht
        omega
      rw [hfalse]
      rfl
    · intro hnot
      exact False.elim (hnot (mem_range.mpr (by omega)))
  omega
