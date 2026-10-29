import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerRootedReflect

/-!
# cycle_power_rooted_reflect_exact

Topic: combinatorics   Node: 2bea652cec1f

Provenance: helper lemma. Uniform structural route for OP-205 / RT-1, following arXiv:2610.15635. These are helper reductions, not a proof of the open covering value and not a research advance. The upper-vertical core remains an explicit unproved hypothesis.

Reflection of rooted profiles preserves exact pair ownership at every rank length L with0<L<=D; the physical starting point changes from v to -v-(D-L).
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_rooted_reflect_exact
    (D L : ℕ) (hL : 0 < L) (hLD : L ≤ D)
    (x : ℤ → ℕ → Bool)
    (hexact : ∀ v : ℤ, (Finset.range L).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-L)).toNat) = 1) :
    ∀ v : ℤ, (Finset.range L).sum (fun a =>
      (cycle_power_rooted_reflect D x (v-(a : ℤ)) a &&
       cycle_power_rooted_reflect D x (v-(a : ℤ)) (a+D-L)).toNat) = 1 := by
  intro v
  rw [← Finset.sum_range_reflect]
  have hs := hexact (-v-((D-L : ℕ) : ℤ))
  convert hs using 1
  apply Finset.sum_congr rfl
  intro a ha
  have haL : a < L := Finset.mem_range.mp ha
  dsimp [cycle_power_rooted_reflect]
  have hidx₁ : D-1-(L-1-a)=a+D-L := by omega
  have hidx₂ : D-1-((L-1-a)+D-L)=a := by omega
  have hp : -(v-((L-1-a : ℕ) : ℤ))-((D-1 : ℕ) : ℤ) =
      -v-((D-L : ℕ) : ℤ)-(a : ℤ) := by omega
  rw [hidx₁,hidx₂,hp,Bool.and_comm]
