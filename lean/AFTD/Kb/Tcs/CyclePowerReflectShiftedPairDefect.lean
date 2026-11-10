import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerRootedReflect

/-!
# cycle_power_reflect_shifted_pair_defect

Topic: combinatorics   Node: 00d5b7be1366

Provenance: helper lemma. Reflection identities for the two-phase defective half-model route of RT-1.

Reflection transports a defective pair-ownership equation and reverses the phase.
-/

open Finset

theorem cycle_power_reflect_shifted_pair_defect
    (D L : ℕ) (hL : 0 < L) (hLD : L ≤ D)
    (x : ℤ → ℕ → Bool) (e : ℤ → Bool) (shift : ℤ)
    (h : ∀ v : ℤ, (Finset.range L).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-L)).toNat) +
        (e (v+shift)).toNat = 1) :
    ∀ v : ℤ, (Finset.range L).sum (fun a =>
      (cycle_power_rooted_reflect D x (v-(a : ℤ)) a &&
       cycle_power_rooted_reflect D x (v-(a : ℤ)) (a+D-L)).toNat) +
        (e (-v-((D-L : ℕ) : ℤ)+shift)).toNat = 1 := by
  intro v
  rw [← Finset.sum_range_reflect]
  have hs := h (-v-((D-L : ℕ) : ℤ))
  convert hs using 1
  apply congrArg (fun z : ℕ => z + (e (-v-((D-L : ℕ) : ℤ)+shift)).toNat)
  apply Finset.sum_congr rfl
  intro a ha
  have haL : a < L := Finset.mem_range.mp ha
  dsimp [cycle_power_rooted_reflect]
  have hidx₁ : D-1-(L-1-a)=a+D-L := by omega
  have hidx₂ : D-1-((L-1-a)+D-L)=a := by omega
  have hp : -(v-((L-1-a : ℕ) : ℤ))-((D-1 : ℕ) : ℤ) =
      -v-((D-L : ℕ) : ℤ)-(a : ℤ) := by omega
  rw [hidx₁,hidx₂,hp,Bool.and_comm]
