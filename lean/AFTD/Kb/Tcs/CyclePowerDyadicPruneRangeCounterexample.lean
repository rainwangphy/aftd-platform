import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_prune_range_counterexample

Topic: combinatorics   Node: 43a1841cc6ce

Provenance: helper lemma. Auxiliary route audit for OP-205 / RT-1, following arXiv:2610.15635 Section 3. Experiment 6286 minimizes the countermodel to the stronger extremal-count shortcut tried in this campaign session. No graph covering bound or research advance is claimed.

There is a period-12 tight radius-16 class model with exact dyadic long-edge coverage and full ordinary coverage, whose original active counts are all at least four but whose outer-quarter pruned count at zero is two. Thus pruning need not lower the minimum active count by at most one. The original counts vary; this is not a counterexample to constant-count pruning or OP-205.
-/

open Finset

set_option maxHeartbeats 4000000 in
theorem cycle_power_dyadic_prune_range_counterexample_finite :
    ∃ x : ZMod 12 → ℕ → Bool,
      (∀ p, cycle_power_dyadic_class_weight 4 (x p) =
        (range 16).sum (fun a => (x p a).toNat)) ∧
      (∀ (j : Fin 4) (v : ZMod 12),
        (range (2 ^ (j : ℕ))).sum (fun a =>
          (x (v - (a : ZMod 12)) a &&
            x (v - (a : ZMod 12)) (a + 16 - 2 ^ (j : ℕ))).toNat) = 1) ∧
      (∀ (d : Fin 15) (v : ZMod 12),
        ∃ a ∈ range (16 - ((d : ℕ) + 1)),
          x (v - (a : ZMod 12)) a = true ∧
            x (v - (a : ZMod 12)) (a + ((d : ℕ) + 1)) = true) ∧
      (∀ v : ZMod 12, 4 ≤ (range 16).sum (fun a =>
        (x (v - (a : ZMod 12)) a).toNat)) ∧
      (range 8).sum (fun a =>
        (cycle_power_dyadic_b_lift 2 (x (-(a : ZMod 12))) a).toNat) = 2 := by
  let x : ZMod 12 → ℕ → Bool := fun p j => decide (j ∈
    match p.val with
    | 0 => ({0, 1, 2, 3, 4, 9, 10, 11, 12, 13, 14, 15} : Finset ℕ)
    | 1 => {0, 15}
    | 2 => {0, 14, 15}
    | 3 => {0, 1, 13, 14, 15}
    | 4 => {0, 15}
    | 5 => range 16
    | 6 => {0, 15}
    | 7 => {0, 1, 14, 15}
    | 8 => {0, 15}
    | 9 => {0, 1, 2, 12, 13, 14, 15}
    | 10 => {0, 15}
    | _ => {0, 14, 15})
  refine ⟨x, ?_⟩
  decide

theorem cycle_power_dyadic_prune_range_counterexample :
    ∃ x : ℤ → ℕ → Bool,
      (∀ p j, x (p + 12) j = x p j) ∧
      (∀ p, cycle_power_dyadic_class_weight 4 (x p) =
        (range 16).sum (fun a => (x p a).toNat)) ∧
      (∀ j < 4, ∀ v : ℤ,
        (range (2 ^ j)).sum (fun a =>
          (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 16 - 2 ^ j)).toNat) = 1) ∧
      (∀ d : ℕ, 1 ≤ d → d < 16 → ∀ v : ℤ,
        ∃ a ∈ range (16 - d),
          x (v - (a : ℤ)) a = true ∧ x (v - (a : ℤ)) (a + d) = true) ∧
      (∀ v : ℤ, 4 ≤ (range 16).sum (fun a => (x (v - (a : ℤ)) a).toNat)) ∧
      (range 8).sum (fun a =>
        (cycle_power_dyadic_b_lift 2 (x (-(a : ℤ))) a).toNat) = 2 := by
  obtain ⟨x, hw, he, hc, hmin, hp⟩ := cycle_power_dyadic_prune_range_counterexample_finite
  refine ⟨fun p j => x (p : ZMod 12) j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p j
    simp only [Int.cast_add, Int.cast_ofNat]
    have hz : (12 : ZMod 12) = 0 := by decide
    rw [hz, add_zero]
  · intro p
    exact hw (p : ZMod 12)
  · intro j hj v
    simpa only [Int.cast_sub, Int.cast_natCast] using he ⟨j, hj⟩ (v : ZMod 12)
  · intro d hd hd16 v
    have hi : d - 1 < 15 := by omega
    have hd' : d - 1 + 1 = d := by omega
    obtain ⟨a, ha, h1, h2⟩ := hc ⟨d - 1, hi⟩ (v : ZMod 12)
    simp only [hd'] at ha h1 h2
    exact ⟨a, ha, by simpa only [Int.cast_sub, Int.cast_natCast] using h1,
      by simpa only [Int.cast_sub, Int.cast_natCast] using h2⟩
  · intro v
    simpa only [Int.cast_sub, Int.cast_natCast] using hmin (v : ZMod 12)
  · simpa only [Int.cast_neg, Int.cast_natCast] using hp
