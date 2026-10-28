import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTwoFullRootsPairCrosses
import AFTD.Kb.Tcs.CyclePowerDyadicTwoFullRootsOverlapEmpty
import AFTD.Kb.Tcs.CyclePowerDyadicExactEndpoints
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightAsTreeEdges
import AFTD.Kb.Tcs.CyclePowerGapLeftSide
import AFTD.Kb.Tcs.CyclePowerGapRightSide
import AFTD.Kb.Tcs.CyclePowerGapSidesCard
import AFTD.Kb.Tcs.CyclePowerGapSidesPairCard

/-!
# cycle_power_dyadic_gap_side_tree

Topic: combinatorics   Node: 2ca0158c7269

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

Between two full roots at distance g at most the radius, the compressed sides of every interior tight class satisfy the tree identity: total side size is one plus the sum of its dyadic forward pair counts.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_gap_side_tree
    (m : ℕ) (hm : 1 ≤ m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p : ℤ, cycle_power_dyadic_class_weight m (x p) =
      (range (2^m)).sum (fun i => (x p i).toNat))
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (g : ℕ) (hg : g ≤ 2^m)
    (hfull₀ : ∀ i < 2^m, x 0 i = true)
    (hfullg : ∀ i < 2^m, x (g : ℤ) i = true) :
    ∀ r : Fin (g-1),
      (cycle_power_gap_left_side g (r.val+1) (x ((r.val+1 : ℕ) : ℤ))).card +
      (cycle_power_gap_right_side (2^m) g (r.val+1) (x ((r.val+1 : ℕ) : ℤ))).card =
      1 + (range m).sum (fun j =>
        (((cycle_power_gap_left_side g (r.val+1) (x ((r.val+1 : ℕ) : ℤ))).product
          (cycle_power_gap_right_side (2^m) g (r.val+1) (x ((r.val+1 : ℕ) : ℤ)))).filter
            (fun p : Fin g × Fin g => p.2.val+2^j = p.1.val)).card) := by
  intro r
  have hr₀ : 0 < r.val+1 := by omega
  have hrg : r.val+1 < g := by have := r.isLt; omega
  have hgap := cycle_power_dyadic_two_full_roots_overlap_empty
    m hm x htight hexact g hg hfull₀ hfullg (r.val+1) hr₀ hrg
  have hcard := cycle_power_gap_sides_card (2^m) g (r.val+1) hg hrg
    (x ((r.val+1 : ℕ) : ℤ)) hgap
  have hends := cycle_power_dyadic_exact_endpoints m hm x hexact ((r.val+1 : ℕ) : ℤ)
  rw [← hcard, ← htight, cycle_power_dyadic_class_weight_as_tree_edges m hm _ hends]
  congr 1
  apply sum_congr rfl
  intro j hj
  exact cycle_power_gap_sides_pair_card (2^m) (2^j) g (r.val+1)
    (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt (mem_range.mp hj))) hg hrg
    (x ((r.val+1 : ℕ) : ℤ))
    (cycle_power_dyadic_two_full_roots_pair_crosses m x hexact g hg
      hfull₀ hfullg (r.val+1) hr₀ hrg j (mem_range.mp hj))
