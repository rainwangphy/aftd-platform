import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerRootedReflect

/-!
# cycle_power_reflect_count_defect

Topic: combinatorics   Node: 030b43e7996a

Provenance: helper lemma. Reflection identities for the two-phase defective half-model route of RT-1.

Reflection transports a pointwise active-count defect by negating its vertex.
-/

open Finset

theorem cycle_power_reflect_count_defect
    (D : ℕ) (hD : 0 < D) (x : ℤ → ℕ → Bool) (e : ℤ → Bool) (k : ℕ)
    (h : ∀ v : ℤ, (Finset.range D).sum (fun a => (x (v-(a : ℤ)) a).toNat) +
      (e v).toNat = k) :
    ∀ v : ℤ, (Finset.range D).sum (fun a =>
      (cycle_power_rooted_reflect D x (v-(a : ℤ)) a).toNat) + (e (-v)).toNat = k := by
  intro v
  rw [← Finset.sum_range_reflect]
  have hs := h (-v)
  convert hs using 1
  apply congrArg (fun z : ℕ => z + (e (-v)).toNat)
  apply Finset.sum_congr rfl
  intro a ha
  have haD : a < D := Finset.mem_range.mp ha
  dsimp [cycle_power_rooted_reflect]
  have hi : D-1-(D-1-a)=a := by omega
  have hp : -(v-((D-1-a : ℕ) : ℤ))-((D-1 : ℕ) : ℤ) = -v-(a : ℤ) := by omega
  rw [hi,hp]
