import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassInternalNeighbour
import AFTD.Kb.Tcs.CyclePowerDyadicTwoFullRootsPairCrosses

/-!
# cycle_power_dyadic_two_full_roots_overlap_empty

Topic: combinatorics   Node: de0caa09a2de

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

In a tight exact dyadic model, an interior class between full roots zero and g, with g at most the radius, cannot select a vertex in the overlap of those two full blocks.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_two_full_roots_overlap_empty
    (m : ℕ) (hm : 1 ≤ m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p : ℤ, cycle_power_dyadic_class_weight m (x p) =
      (range (2^m)).sum (fun i => (x p i).toNat))
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (g : ℕ) (hg : g ≤ 2^m)
    (hfull₀ : ∀ i < 2^m, x 0 i = true)
    (hfullg : ∀ i < 2^m, x (g : ℤ) i = true)
    (r : ℕ) (hr₀ : 0 < r) (hrg : r < g)
    (a : ℕ) (ha : a < 2^m) (hba : x (r : ℤ) a = true) :
    r+a < g ∨ 2^m ≤ r+a := by
  by_contra hn
  have ha₀ : 0 < a := by omega
  have haD : a < 2^m-1 := by omega
  obtain ⟨j, hj₀, hjm, i, hi, h₀, h₁, he⟩ :=
    cycle_power_dyadic_tight_class_internal_neighbour m hm (x (r : ℤ))
      (htight (r : ℤ)) a ha₀ haD hba
  have hcross := cycle_power_dyadic_two_full_roots_pair_crosses
    m x hexact g hg hfull₀ hfullg r hr₀ hrg j hjm i hi h₀ h₁
  rcases he with he | he <;> omega
