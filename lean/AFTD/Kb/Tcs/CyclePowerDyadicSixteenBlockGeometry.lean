import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerSixteenBlockNoVerticalOverlap
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicExactEndpoints
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_sixteen_block_geometry

Topic: combinatorics   Node: 5f9822fb9e53

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635. The main covering theorem and vertical-defect exclusion remain open. Experiments8048/8049 suggested the two ordinary distances; the proof is uniform in h and uses Lean only. No advance flag.

Every tight dyadic rooted model of radius2^(k+4), with all-rank exactness, full ordinary coverage and monotone outer eighths, satisfies the explicit sixteen-block Geometry conditions at h=2^k. This is a faithful bridge with no graph-covering conclusion.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_sixteen_block_geometry
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k+4) (x p) =
      (range (2^(k+4))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < k+4, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(k+4)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(k+4) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(k+4)-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true)
    (houter : ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2^(k+1) → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 7*2^(k+1) ≤ a → a ≤ b → b < 2^(k+4) → x p a = true → x p b = true))
 : CyclePowerSixteenBlock.Geometry (2^k) x := by
  let h := 2^k
  have h1 : 2^(k+1)=2*h := by dsimp [h]; rw [pow_succ]; omega
  have h2 : 2^(k+2)=4*h := by rw [show k+2=(k+1)+1 by omega,pow_succ,h1]; omega
  have h3 : 2^(k+3)=8*h := by rw [show k+3=(k+2)+1 by omega,pow_succ,h2]; omega
  have h4 : 2^(k+4)=16*h := by rw [show k+4=(k+3)+1 by omega,pow_succ,h3]; omega
  have hp4 : ∀ p a, a < 8*h →
      (a < 4*h → x p (a+8*h) = true → x p a = true) ∧
      (4*h ≤ a → x p a = true → x p (a+8*h) = true) := by
    intro r a ha
    have hp := cycle_power_dyadic_tight_class_parent (k+4) (k+3) (by omega) (by omega) (x r) (htight r) a (by omega)
    have hi : a+2^(k+4)-2^(k+3)=a+8*h := by omega
    simpa only [show k+3-1=k+2 by omega,h2,hi] using hp
  have hp6 : ∀ p a, a < 4*h →
      (a < 2*h → x p (a+12*h) = true → x p a = true) ∧
      (2*h ≤ a → x p a = true → x p (a+12*h) = true) := by
    intro r a ha
    have hp := cycle_power_dyadic_tight_class_parent (k+4) (k+2) (by omega) (by omega) (x r) (htight r) a (by omega)
    have hi : a+2^(k+4)-2^(k+2)=a+12*h := by omega
    simpa only [show k+2-1=k+1 by omega,h1,hi] using hp
  have hp7 : ∀ p a, a < 2*h →
      (a < h → x p (a+14*h) = true → x p a = true) ∧
      (h ≤ a → x p a = true → x p (a+14*h) = true) := by
    intro r a ha
    have hp := cycle_power_dyadic_tight_class_parent (k+4) (k+1) (by omega) (by omega) (x r) (htight r) a (by omega)
    have hi : a+2^(k+4)-2^(k+1)=a+14*h := by omega
    simpa only [show k+1-1=k by omega,hi] using hp
  have he6 : ∀ v : ℤ, (range (4*h)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+12*h)).toNat) = 1 := by
    intro v
    have hi (a : ℕ) : a+16*h-4*h=a+12*h := by omega
    simpa only [h4,h2,hi] using hexact (k+2) (by omega) v
  have he7 : ∀ v : ℤ, (range (2*h)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+14*h)).toNat) = 1 := by
    intro v
    have hi (a : ℕ) : a+16*h-2*h=a+14*h := by omega
    simpa only [h4,h1,hi] using hexact (k+1) (by omega) v
  have he15 : ∀ v : ℤ, (range h).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+15*h)).toNat) = 1 := by
    intro v
    have hi (a : ℕ) : a+16*h-h=a+15*h := by omega
    simpa only [h4,show 2^k=h by rfl,hi] using hexact k (by omega) v
  have M : CyclePowerSixteenBlock.Geometry h x := {
    pos := Nat.two_pow_pos k
    ends := by simpa only [h4] using cycle_power_dyadic_exact_endpoints (k+4) (by omega) x hexact
    lowMono := by simpa only [h1] using fun p => (houter p).1
    highMono := by simpa only [h1,h4,show 7*(2*h)=14*h by omega] using fun p => (houter p).2
    parent4 := hp4
    parent6 := hp6
    parent7 := hp7
    exact6 := he6
    exact7 := he7
    exact15 := he15
    cover := by simpa only [h4] using hcover }
  exact M
