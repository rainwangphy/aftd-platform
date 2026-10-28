import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEightBlockActiveRetainedHalves
import AFTD.Kb.Tcs.CyclePowerExactPairUnique

/-!
# cycle_power_eight_block_active_root_separation

Topic: combinatorics   Node: 077df1a7f328

Provenance: helper lemma. Supporting uniform structural route for OP-205 / RT-1 following arXiv:2610.15635. No unconditional shape theorem or main covering result is claimed. No advance flag.

Under the explicit third parent, monotone outer eighths and exact distance15h ownership, distinct roots selecting an A/Z overlap are separated by at least h.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_eight_block_active_root_separation
    (h : ℕ) (hh : 0 < h) (x : ℤ → ℕ → Bool)
    (hparent7 : ∀ p a, a < 2*h →
      (a < h → x p (a+14*h) = true → x p a = true) ∧
      (h ≤ a → x p a = true → x p (a+14*h) = true))
    (houter : ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2*h → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 14*h ≤ a → a ≤ b → b < 16*h → x p a = true → x p b = true))
    (h15 : ∀ v : ℤ, (range h).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+15*h)).toNat) = 1)
    (p : ℤ) (r t u : ℕ) (hr : 0 < r) (ht : t < 2*h) (hu : u < 2*h)
    (hpA : x p t = true) (hpB : x p (14*h+t) = true)
    (hrA : x (p+(r : ℤ)) u = true) (hrB : x (p+(r : ℤ)) (14*h+u) = true) :
    h ≤ r := by
  by_contra hn
  have hpr := cycle_power_eight_block_active_retained_halves h x hparent7 houter p t ht hpA hpB
  have hrr := cycle_power_eight_block_active_retained_halves h x hparent7 houter (p+(r : ℤ)) u hu hrA hrB
  have h15' : ∀ v : ℤ, (range h).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+16*h-h)).toNat) = 1 := by
    intro v
    have hi (a : ℕ) : a+16*h-h=a+15*h := by omega
    simpa only [hi] using h15 v
  have he := cycle_power_exact_pair_unique (16*h) h x h15' (p+(r : ℤ)) r 0
    (by omega) hh
    (by simpa using (hpr r (by omega)).1)
    (by simpa only [add_sub_cancel_right,show r+16*h-h=15*h+r by omega] using (hpr r (by omega)).2)
    (by simpa using (hrr 0 hh).1)
    (by simpa only [Nat.cast_zero,sub_zero,show 0+16*h-h=15*h+0 by omega] using (hrr 0 hh).2)
  omega
