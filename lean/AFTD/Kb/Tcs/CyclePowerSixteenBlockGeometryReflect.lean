import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerSixteenBlockNoVerticalOverlap
import AFTD.Kb.Tcs.CyclePowerRootedReflect
import AFTD.Kb.Tcs.CyclePowerRootedReflectExact
import AFTD.Kb.Tcs.CyclePowerRootedReflectCover
import AFTD.Kb.Tcs.CyclePowerRootedReflectParent

/-!
# cycle_power_sixteen_block_geometry_reflect

Topic: combinatorics   Node: b7f9c92f045d

Provenance: helper lemma. Uniform structural route for OP-205 / RT-1, following arXiv:2610.15635. These are helper reductions, not a proof of the open covering value and not a research advance. The upper-vertical core remains an explicit unproved hypothesis.

The full radius16h Geometry hypotheses, including all ordinary distances and exact12h/14h/15h ownership, are preserved by simultaneous root and offset reflection.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_sixteen_block_geometry_reflect
    (h : ℕ) (x : ℤ → ℕ → Bool) (M : CyclePowerSixteenBlock.Geometry h x) :
    CyclePowerSixteenBlock.Geometry h (cycle_power_rooted_reflect (16*h) x) := by
  have hp := M.pos
  have i4 (a : ℕ) : a+16*h-8*h=a+8*h := by omega
  have i6 (a : ℕ) : a+16*h-4*h=a+12*h := by omega
  have i7 (a : ℕ) : a+16*h-2*h=a+14*h := by omega
  have p4 : ∀ p a, a < 2*(4*h) →
      (a < 4*h → x p (a+16*h-2*(4*h)) = true → x p a = true) ∧
      (4*h ≤ a → x p a = true → x p (a+16*h-2*(4*h)) = true) := by
    simpa only [i4,show 2*(4*h)=8*h by omega] using M.parent4
  have p6 : ∀ p a, a < 2*(2*h) →
      (a < 2*h → x p (a+16*h-2*(2*h)) = true → x p a = true) ∧
      (2*h ≤ a → x p a = true → x p (a+16*h-2*(2*h)) = true) := by
    simpa only [i6,show 2*(2*h)=4*h by omega] using M.parent6
  have p7 : ∀ p a, a < 2*h →
      (a < h → x p (a+16*h-2*h) = true → x p a = true) ∧
      (h ≤ a → x p a = true → x p (a+16*h-2*h) = true) := by
    simpa only [i7] using M.parent7
  have e6 : ∀ v : ℤ, (Finset.range (4*h)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+16*h-4*h)).toNat) = 1 := by
    simpa only [show ∀ a : ℕ, a+16*h-4*h=a+12*h by omega] using M.exact6
  have e7 : ∀ v : ℤ, (Finset.range (2*h)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+16*h-2*h)).toNat) = 1 := by
    simpa only [i7] using M.exact7
  have e15 : ∀ v : ℤ, (Finset.range h).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+16*h-h)).toNat) = 1 := by
    simpa only [show ∀ a : ℕ, a+16*h-h=a+15*h by omega] using M.exact15
  refine {
    pos := hp
    ends := ?_
    lowMono := ?_
    highMono := ?_
    parent4 := ?_
    parent6 := ?_
    parent7 := ?_
    exact6 := ?_
    exact7 := ?_
    exact15 := ?_
    cover := ?_ }
  · intro p
    simpa only [cycle_power_rooted_reflect,Nat.sub_zero,Nat.sub_self] using
      (M.ends (-p-((16*h-1 : ℕ) : ℤ))).symm
  · intro p a b hab hb hx
    have hh := M.highMono (-p-((16*h-1 : ℕ) : ℤ)) (16*h-1-b) (16*h-1-a)
      (by omega) (by omega) (by omega) hx
    exact hh
  · intro p a b ha hab hb hx
    have hh := M.lowMono (-p-((16*h-1 : ℕ) : ℤ)) (16*h-1-b) (16*h-1-a)
      (by omega) (by omega) hx
    exact hh
  · simpa only [i4,show 2*(4*h)=8*h by omega] using
      cycle_power_rooted_reflect_parent (16*h) (4*h) (by omega) (by omega) x p4
  · simpa only [i6,show 2*(2*h)=4*h by omega] using
      cycle_power_rooted_reflect_parent (16*h) (2*h) (by omega) (by omega) x p6
  · simpa only [i7] using
      cycle_power_rooted_reflect_parent (16*h) h hp (by omega) x p7
  · simpa only [show ∀ a : ℕ, a+16*h-4*h=a+12*h by omega] using
      cycle_power_rooted_reflect_exact (16*h) (4*h) (by omega) (by omega) x e6
  · simpa only [i7] using
      cycle_power_rooted_reflect_exact (16*h) (2*h) (by omega) (by omega) x e7
  · simpa only [show ∀ a : ℕ, a+16*h-h=a+15*h by omega] using
      cycle_power_rooted_reflect_exact (16*h) h hp (by omega) x e15
  · exact cycle_power_rooted_reflect_cover (16*h) (by omega) x M.cover
