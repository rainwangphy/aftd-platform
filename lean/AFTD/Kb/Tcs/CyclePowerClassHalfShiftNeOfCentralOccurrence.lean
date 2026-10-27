import AFTD.Prelude

/-!
# cycle_power_class_half_shift_ne_of_central_occurrence

Topic: combinatorics   Node: a87eaa7108b2

Provenance: helper lemma. Uniform helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The neighbour-weight induction and central occurrence are class-model helpers; they do not prove the unresolved covering number. No research advance is claimed.

A central occurrence in bounded rooted classes with proper labels forces some two root labels to differ after a half-radius shift. The left central occurrence uses the preceding class endpoint; this requires no endpoint-overlap assumption.
-/

open Finset

theorem cycle_power_class_half_shift_ne_of_central_occurrence
    {α : Type*} (H : ℕ) (hH : 0 < H)
    (x : ℤ → ℕ → Bool) (ell : ℤ → α)
    (hroot : ∀ p : ℤ, x p 0 = true ∧ x p (2*H-1) = true)
    (hsep : ∀ (v : ℤ) (a b : ℕ), a < 2*H → b < 2*H → a ≠ b →
      x (v-(a : ℤ)) a = true → x (v-(b : ℤ)) b = true →
        ell (v-(a : ℤ)) ≠ ell (v-(b : ℤ)))
    (hcentral : ∃ p : ℤ, x p (H-1) = true ∨ x p H = true) :
    ∃ p : ℤ, ell (p+(H : ℤ)) ≠ ell p := by
  obtain ⟨p, hp | hp⟩ := hcentral
  · let v : ℤ := p+(H : ℤ)-1
    have hv0 : v-((2*H-1 : ℕ) : ℤ)=p-(H : ℤ) := by dsimp [v]; omega
    have hv1 : v-((H-1 : ℕ) : ℤ)=p := by dsimp [v]; omega
    have hs := hsep v (2*H-1) (H-1) (by omega) (by omega) (by omega)
      (by rw [hv0]; exact (hroot (p-(H : ℤ))).2) (by rw [hv1]; exact hp)
    rw [hv0, hv1] at hs
    refine ⟨p-(H : ℤ), ?_⟩
    simpa only [sub_add_cancel] using hs.symm
  · let v : ℤ := p+(H : ℤ)
    have hv0 : v-(H : ℤ)=p := by dsimp [v]; omega
    have hs := hsep v H 0 (by omega) (by omega) (by omega)
      (by rw [hv0]; exact hp)
      (by simpa only [Nat.cast_zero, sub_zero] using (hroot v).1)
    rw [hv0] at hs
    refine ⟨p, ?_⟩
    simpa only [Nat.cast_zero, sub_zero] using hs.symm
