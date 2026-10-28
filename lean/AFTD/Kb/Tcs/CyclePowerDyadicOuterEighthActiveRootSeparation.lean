import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEightBlockActiveRootSeparation
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent

/-!
# cycle_power_dyadic_outer_eighth_active_root_separation

Topic: combinatorics   Node: bb9959dcd512

Provenance: helper lemma. Supporting uniform structural route for OP-205 / RT-1 following arXiv:2610.15635. No unconditional shape theorem or main covering result is claimed. No advance flag.

In a tight model of radius2^(k+4) with monotone outer eighths and exact rank k ownership, two active seven-eighth roots are separated by at least2^k. No counts, periodicity or other ordinary-coverage hypotheses are needed.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_outer_eighth_active_root_separation
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k+4) (x p) =
      (range (2^(k+4))).sum (fun a => (x p a).toNat))
    (hexact : ∀ v : ℤ, (range (2^k)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(k+4)-2^k)).toNat) = 1)
    (houter : ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2^(k+1) → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 7*2^(k+1) ≤ a → a ≤ b → b < 2^(k+4) → x p a = true → x p b = true))
    (p : ℤ) (r t u : ℕ) (hr : 0 < r) (ht : t < 2^(k+1)) (hu : u < 2^(k+1))
    (hpA : x p t = true) (hpB : x p (7*2^(k+1)+t) = true)
    (hrA : x (p+(r : ℤ)) u = true) (hrB : x (p+(r : ℤ)) (7*2^(k+1)+u) = true) :
    2^k ≤ r := by
  let h := 2^k
  have hH : 2^(k+1)=2*h := by dsimp [h]; rw [pow_succ]; omega
  have hD : 2^(k+4)=16*h := by rw [show k+4=k+4 by rfl,pow_add]; norm_num; dsimp [h]; omega
  have hp7 : ∀ p a, a < 2*h →
      (a < h → x p (a+14*h) = true → x p a = true) ∧
      (h ≤ a → x p a = true → x p (a+14*h) = true) := by
    intro p a ha
    have hp := cycle_power_dyadic_tight_class_parent (k+4) (k+1) (by omega) (by omega) (x p) (htight p)
      a (by omega)
    have hi : a+2^(k+4)-2^(k+1)=a+14*h := by omega
    simpa only [show k+1-1=k by omega,hi] using hp
  have he : ∀ v : ℤ, (range h).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+15*h)).toNat) = 1 := by
    intro v
    have hi (a : ℕ) : a+2^(k+4)-2^k=a+15*h := by dsimp [h] at *; omega
    simpa only [hi] using hexact v
  apply cycle_power_eight_block_active_root_separation h (Nat.two_pow_pos k) x hp7
    (by simpa only [hH,hD,show 7*(2*h)=14*h by omega] using houter) he p r t u hr
    (by omega) (by omega) hpA _ hrA _
  · simpa only [hH,show 7*(2*h)=14*h by omega] using hpB
  · simpa only [hH,show 7*(2*h)=14*h by omega] using hrB
