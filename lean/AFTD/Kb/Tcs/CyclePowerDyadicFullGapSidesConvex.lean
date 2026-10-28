import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicExactEndpoints
import AFTD.Kb.Tcs.OrderedBicliqueDyadicTreeIntervals
import AFTD.Kb.Tcs.CyclePowerGapLeftSide
import AFTD.Kb.Tcs.CyclePowerGapRightSide
import AFTD.Kb.Tcs.CyclePowerGapOrdinarySideCover
import AFTD.Kb.Tcs.CyclePowerGapExactSideOwner
import AFTD.Kb.Tcs.CyclePowerDyadicGapSideTree

/-!
# cycle_power_dyadic_full_gap_sides_convex

Topic: combinatorics   Node: 51e17b203899

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

In a tight exact full ordinary-coverage dyadic model, all compressed sides between full roots zero and g are intervals when g lies between half and the full radius.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_full_gap_sides_convex
    (m : ℕ) (hm : 1 ≤ m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p : ℤ, cycle_power_dyadic_class_weight m (x p) =
      (range (2^m)).sum (fun i => (x p i).toNat))
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^m-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true)
    (g : ℕ) (hlo : 2^(m-1) ≤ g) (hg : g ≤ 2^m)
    (hfull₀ : ∀ i < 2^m, x 0 i = true)
    (hfullg : ∀ i < 2^m, x (g : ℤ) i = true) :
    let A : Fin (g-1) → Finset (Fin g) := fun r =>
      cycle_power_gap_left_side g (r.val+1) (x ((r.val+1 : ℕ) : ℤ))
    let B : Fin (g-1) → Finset (Fin g) := fun r =>
      cycle_power_gap_right_side (2^m) g (r.val+1) (x ((r.val+1 : ℕ) : ℤ))
    (∀ r (i j k : Fin g), i ≤ j → j ≤ k → i ∈ A r → k ∈ A r → j ∈ A r) ∧
    (∀ r (i j k : Fin g), i ≤ j → j ≤ k → i ∈ B r → k ∈ B r → j ∈ B r) := by
  classical
  dsimp only
  apply ordered_biclique_dyadic_tree_intervals g m hm hlo
  · intro r i hi
    have := (mem_filter.mp hi).2.1
    omega
  · intro r i hi
    have := (mem_filter.mp hi).2.1
    omega
  · intro r
    have hrg : r.val+1 < g := by have := r.isLt; omega
    let i : Fin g := ⟨r.val+1, hrg⟩
    have hend := (cycle_power_dyadic_exact_endpoints m hm x hexact
      ((r.val+1 : ℕ) : ℤ)).1
    refine ⟨i, mem_union.mpr (Or.inl ?_)⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _, le_rfl, ?_⟩
    simpa only [i, Nat.sub_self] using hend
  · exact cycle_power_gap_ordinary_side_cover (2^m) g hg x hcover
  · exact cycle_power_dyadic_gap_side_tree m hm x htight hexact g hg hfull₀ hfullg
  · intro j hj
    exact cycle_power_gap_exact_side_owner (2^m) (2^j) g
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hj)) hg x (hexact j hj)
