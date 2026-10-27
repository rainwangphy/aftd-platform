import AFTD.Prelude

/-!
# cycle_power_alternating_paired_compression_cover

Topic: combinatorics   Node: cb0265676e68

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635, Section 3. These conditional class-system and pruning lemmas do not establish the unresolved graph covering bound. The earlier fixed-radius helpers handle radii eight and sixteen; this session works with arbitrary dyadic radii. No research advance is claimed.

If all even-start classes are endpoint-only and all original distances less than 2h are covered, the odd-start classes, compressed to their even ages, cover every distance less than h.
-/

open Finset

theorem cycle_power_alternating_paired_compression_cover
    (h : ℕ) (x : ℤ → ℕ → Bool)
    (heven : ∀ p : ℤ, ∀ j < 2 * h,
      x (2 * p) j = true ↔ j = 0 ∨ j = 2 * h - 1)
    (hcover : ∀ d, 1 ≤ d → d < 2 * h → ∀ u : ℤ,
      ∃ a < 2 * h - d, x (u - (a : ℤ)) a = true ∧
        x (u - (a : ℤ)) (a + d) = true) :
    ∀ d, 1 ≤ d → d < h → ∀ u : ℤ,
      ∃ a < h - d, x (2 * (u - (a : ℤ)) + 1) (2 * a) = true ∧
        x (2 * (u - (a : ℤ)) + 1) (2 * (a + d)) = true := by
  intro d hd hdh u
  obtain ⟨a, ha, h0, h1⟩ := hcover (2 * d) (by omega) (by omega) (2 * u + 1)
  have he : a % 2 = 0 := by
    by_contra hodd
    have har : a = 2 * (a / 2) + 1 := by omega
    have hstart : 2 * u + 1 - (a : ℤ) = 2 * (u - (a / 2 : ℕ)) := by omega
    rw [hstart] at h0
    have hh := (heven _ a (by omega)).mp h0
    omega
  have har : a = 2 * (a / 2) := by omega
  have hstart : 2 * u + 1 - (a : ℤ) = 2 * (u - (a / 2 : ℕ)) + 1 := by omega
  refine ⟨a / 2, by omega, ?_, ?_⟩
  · have hi : 2 * (a / 2) = a := by omega
    rw [hi]
    simpa only [hstart] using h0
  · have hi : a + 2 * d = 2 * (a / 2 + d) := by omega
    simpa only [hstart, hi] using h1
