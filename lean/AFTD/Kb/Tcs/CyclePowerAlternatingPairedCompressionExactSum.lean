import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerSumRangeDouble

/-!
# cycle_power_alternating_paired_compression_exact_sum

Topic: combinatorics   Node: a496a91624c3

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635, Section 3. These conditional class-system and pruning lemmas do not establish the unresolved graph covering bound. The earlier fixed-radius helpers handle radii eight and sixteen; this session works with arbitrary dyadic radii. No research advance is claimed.

For a positive distance d and s+d at most h, the original sum over 2s possible witnesses for distance 2d at an odd vertex equals the compressed sum over s witnesses for distance d, provided all even-start classes are endpoint-only.
-/

open Finset

theorem cycle_power_alternating_paired_compression_exact_sum
    (h d s : ℕ) (hd : 0 < d) (hds : s + d ≤ h) (x : ℤ → ℕ → Bool)
    (heven : ∀ p : ℤ, ∀ j < 2 * h,
      x (2 * p) j = true ↔ j = 0 ∨ j = 2 * h - 1) :
    ∀ u : ℤ,
      (range (2 * s)).sum (fun a =>
        (x (2 * u + 1 - (a : ℤ)) a &&
          x (2 * u + 1 - (a : ℤ)) (a + 2 * d)).toNat) =
      (range s).sum (fun a =>
        (x (2 * (u - (a : ℤ)) + 1) (2 * a) &&
          x (2 * (u - (a : ℤ)) + 1) (2 * (a + d))).toNat) := by
  intro u
  rw [cycle_power_sum_range_double]
  apply sum_congr rfl
  intro a ha
  have hal : a < s := mem_range.mp ha
  have hevenstart : 2 * u + 1 - ((2 * a : ℕ) : ℤ) = 2 * (u - (a : ℤ)) + 1 := by
    push_cast; ring
  have hoddstart : 2 * u + 1 - ((2 * a + 1 : ℕ) : ℤ) = 2 * (u - (a : ℤ)) := by
    push_cast; ring
  have hfalse : x (2 * (u - (a : ℤ))) (2 * a + 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have := (heven _ _ (by omega)).mp ht
    omega
  rw [hevenstart, hoddstart, hfalse]
  have hi : 2 * a + 2 * d = 2 * (a + d) := by omega
  simp only [Bool.false_and, Bool.toNat_false, add_zero, hi]
