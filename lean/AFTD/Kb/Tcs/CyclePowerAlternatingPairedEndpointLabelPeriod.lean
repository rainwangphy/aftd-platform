import AFTD.Prelude

/-!
# cycle_power_alternating_paired_endpoint_label_period

Topic: combinatorics   Node: 77ee70a3df15

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635, Section 3. These conditional class-system and pruning lemmas do not establish the unresolved graph covering bound. The earlier fixed-radius helpers handle radii eight and sixteen; this session works with arbitrary dyadic radii. No research advance is claimed.

For classes on the integer line of any positive even arc length 2h, assume even-start classes contain exactly their two endpoints, odd-start classes have equal consecutive bits, every label occurs in a class at each vertex, and classes with the same label cannot overlap. Then each even-start label repeats after 2h. The label type is arbitrary.
-/

open Finset

theorem cycle_power_alternating_paired_endpoint_label_period
    {α : Type*} (h : ℕ) (hh : 0 < h)
    (x : ℤ → ℕ → Bool) (σ : ℤ → α)
    (heven : ∀ p : ℤ, ∀ j < 2 * h,
      x (2 * p) j = true ↔ j = 0 ∨ j = 2 * h - 1)
    (hpair : ∀ p : ℤ, ∀ j < h,
      x (2 * p + 1) (2 * j) = x (2 * p + 1) (2 * j + 1))
    (hslots : ∀ (v : ℤ) (a : α), ∃ j < 2 * h,
      x (v - (j : ℤ)) j = true ∧ σ (v - (j : ℤ)) = a)
    (hsep : ∀ (v : ℤ) (j k : ℕ), j < 2 * h → k < 2 * h →
      x (v - (j : ℤ)) j = true → x (v - (k : ℤ)) k = true →
      σ (v - (j : ℤ)) = σ (v - (k : ℤ)) → j = k) :
    ∀ p : ℤ, σ (2 * p + 2 * (h : ℤ)) = σ (2 * p) := by
  intro p
  let w : ℤ := 2 * p + 2 * (h : ℤ)
  obtain ⟨j, hj, hxj, hσ⟩ := hslots w (σ (2 * p))
  by_cases he : j % 2 = 0
  · have hwj : w - (j : ℤ) = 2 * (p + (h : ℤ) - (j / 2 : ℕ)) := by
      dsimp [w]; omega
    rw [hwj] at hxj
    have hz := (heven _ j hj).mp hxj
    have hjz : j = 0 := by omega
    subst j
    simpa [w] using hσ
  · have hjodd : j = 2 * (j / 2) + 1 := by omega
    have hr : j / 2 < h := by omega
    let q : ℤ := p + (h : ℤ) - (j / 2 : ℕ) - 1
    have hwj : w - (j : ℤ) = 2 * q + 1 := by
      dsimp [w, q]; omega
    have hjm : j - 1 = 2 * (j / 2) := by omega
    have hprev : x (w - (j : ℤ)) (j - 1) = true := by
      rw [hwj, hjm, hpair q (j / 2) hr]
      simpa [hwj, ← hjodd] using hxj
    let v : ℤ := w - 1
    have hstart : v - ((j - 1 : ℕ) : ℤ) = w - (j : ℤ) := by
      dsimp [v]; omega
    have hendstart : v - ((2 * h - 1 : ℕ) : ℤ) = 2 * p := by
      dsimp [v, w]; omega
    have heidx : 2 * h - 1 < 2 * h := by omega
    have hend : x (v - ((2 * h - 1 : ℕ) : ℤ)) (2 * h - 1) = true := by
      rw [hendstart]
      exact (heven p (2 * h - 1) heidx).mpr (Or.inr rfl)
    have heq := hsep v (j - 1) (2 * h - 1) (by omega) heidx
      (by simpa only [hstart] using hprev) hend
      (by simpa only [hstart, hendstart] using hσ)
    omega
