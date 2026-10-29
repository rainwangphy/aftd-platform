import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerSixteenBlockGeometryReflect
import AFTD.Kb.Tcs.CyclePowerRootedReflectExact
import AFTD.Kb.Tcs.CyclePowerSixteenBlockLeftQuarterOfNoVertical
import AFTD.Kb.Tcs.CyclePowerSixteenBlockNoVerticalOverlap
import AFTD.Kb.Tcs.CyclePowerRootedReflect

/-!
# cycle_power_sixteen_block_outer_quarters_of_upper_vertical

Topic: combinatorics   Node: 4797ef25bafd

Provenance: helper lemma. Uniform structural route for OP-205 / RT-1, following arXiv:2610.15635. These are helper reductions, not a proof of the open covering value and not a research advance. The upper-vertical core remains an explicit unproved hypothesis.

Conditional on upper-half vertical exclusion for every Geometry model at the same h with exact8h ownership, a given such model has BOTH monotone outer quarters. The vertical-exclusion core is explicitly assumed.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_sixteen_block_outer_quarters_of_upper_vertical
    (h : ℕ) (x : ℤ → ℕ → Bool) (M : CyclePowerSixteenBlock.Geometry h x)
    (hexact4 : ∀ v : ℤ, (Finset.range (8*h)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+8*h)).toNat) = 1)
    (hcore : ∀ (y : ℤ → ℕ → Bool), CyclePowerSixteenBlock.Geometry h y →
      (∀ v : ℤ, (Finset.range (8*h)).sum (fun a =>
        (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+8*h)).toNat) = 1) →
      ∀ p t, h ≤ t → t < 2*h → y p (2*h+t) = true → y p t = true) :
    ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 4*h → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 12*h ≤ a → a ≤ b → b < 16*h → x p a = true → x p b = true) := by
  have nov (y : ℤ → ℕ → Bool) (N : CyclePowerSixteenBlock.Geometry h y)
      (he : ∀ v : ℤ, (Finset.range (8*h)).sum (fun a =>
        (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+8*h)).toNat) = 1) :
      ∀ p a, a < 2*h → y p (2*h+a) = true → y p a = true := by
    intro p a ha hc
    by_cases hal : a < h
    · exact (N.parent7 p a ha).1 hal (by simpa only [Nat.add_comm] using N.childZ p a ha hc)
    · exact hcore y N he p a (by omega) ha hc
  have left := cycle_power_sixteen_block_left_quarter_of_no_vertical h x M (nov x M hexact4)
  let y := cycle_power_rooted_reflect (16*h) x
  have N : CyclePowerSixteenBlock.Geometry h y := cycle_power_sixteen_block_geometry_reflect h x M
  have hexact4' : ∀ v : ℤ, (Finset.range (8*h)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+16*h-8*h)).toNat) = 1 := by
    simpa only [show ∀ a : ℕ, a+16*h-8*h=a+8*h by omega] using hexact4
  have ey : ∀ v : ℤ, (Finset.range (8*h)).sum (fun a =>
      (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+8*h)).toNat) = 1 := by
    simpa only [show ∀ a : ℕ, a+16*h-8*h=a+8*h by omega] using
      cycle_power_rooted_reflect_exact (16*h) (8*h) (by have := M.pos; omega) (by omega) x hexact4'
  have right := cycle_power_sixteen_block_left_quarter_of_no_vertical h y N (nov y N ey)
  intro p
  refine ⟨left p,?_⟩
  intro a b ha hab hb hx
  let r := -p-((16*h-1 : ℕ) : ℤ)
  have hy : y r (16*h-1-a) = true := by
    dsimp [y,cycle_power_rooted_reflect,r]
    convert hx using 1 <;> congr 1 <;> have := M.pos <;> omega
  have hz := right r (16*h-1-b) (16*h-1-a) (by omega) (by omega) hy
  dsimp [y,cycle_power_rooted_reflect,r] at hz
  convert hz using 1 <;> congr 1 <;> have := M.pos <;> omega
