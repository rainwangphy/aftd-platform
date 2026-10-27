import AFTD.Prelude

/-!
# cycle_power_no_island_of_half_monotone

Topic: combinatorics   Node: 2986b4dffb0f

Provenance: helper lemma. Uniform conditional structural helper for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The middle-bit fullness assumptions and smaller-quarter monotonicity are explicit when used; no optimal-count classification, graph covering value or research advance is claimed.

A Boolean class which is monotone toward the left endpoint on the left half and toward the right endpoint on the right half has no selected island between two missing offsets.
-/

open Finset

theorem cycle_power_no_island_of_half_monotone
    (H D : ℕ) (x : ℤ → ℕ → Bool)
    (hmono : ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < H → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, H ≤ a → a ≤ b → b < D → x p a = true → x p b = true)) :
    ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < D →
      x p a = false → x p b = true → x p c = true := by
  intro p a b c hab hbc hc ha hb
  by_cases hbl : b < H
  · have hh := (hmono p).1 a b (by omega) hbl hb
    rw [ha] at hh
    contradiction
  · exact (hmono p).2 b c (by omega) (by omega) hc hb
