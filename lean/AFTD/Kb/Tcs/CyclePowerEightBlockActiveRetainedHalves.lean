import AFTD.Prelude

/-!
# cycle_power_eight_block_active_retained_halves

Topic: combinatorics   Node: c4d6f5b8a999

Provenance: helper lemma. Supporting uniform structural route for OP-205 / RT-1 following arXiv:2610.15635. No unconditional shape theorem or main covering result is claimed. No advance flag.

Under the explicit seven-eighth parent and monotone outer eighths, a root selecting A_t and Z_t retains every first-h and last-h offset.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_eight_block_active_retained_halves
    (h : ℕ) (x : ℤ → ℕ → Bool)
    (hparent7 : ∀ p a, a < 2*h →
      (a < h → x p (a+14*h) = true → x p a = true) ∧
      (h ≤ a → x p a = true → x p (a+14*h) = true))
    (houter : ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2*h → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 14*h ≤ a → a ≤ b → b < 16*h → x p a = true → x p b = true))
    (p : ℤ) (t : ℕ) (ht : t < 2*h)
    (hA : x p t = true) (hB : x p (14*h+t) = true) :
    ∀ a < h, x p a = true ∧ x p (15*h+a) = true := by
  intro a ha
  have hb (b : ℕ) (hab : t ≤ b) (hb : b < 2*h) : x p (b+14*h) = true := by
    apply (houter p).2 (14*h+t) (b+14*h) (by omega) (by omega) (by omega)
    simpa only [Nat.add_comm t (14*h)] using hB
  constructor
  · by_cases hat : a ≤ t
    · exact (houter p).1 a t hat ht hA
    · exact (hparent7 p a (by omega)).1 ha (hb a (by omega) (by omega))
  · have hi : 15*h+a=(h+a)+14*h := by omega
    rw [hi]
    by_cases hta : t ≤ h+a
    · exact hb (h+a) hta (by omega)
    · exact (hparent7 p (h+a) (by omega)).2 (by omega)
        ((houter p).1 (h+a) t (by omega) ht hA)
