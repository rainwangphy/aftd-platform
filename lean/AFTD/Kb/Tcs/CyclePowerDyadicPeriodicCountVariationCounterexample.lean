import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_periodic_count_variation_counterexample

Topic: combinatorics   Node: 98b3372f768b

Provenance: helper lemma. Route barrier for OP-205 / RT-1 following arXiv:2610.15635 Section 3; complete Boolean witness found in experiment6550 (with experiment6548 testing larger radii). Finite periodicity and average equality alone do not recover the missing optimal scalar-count hypothesis. No research advance claimed.

Finite period16 radius8 counterexample to recovering pointwise optimal scalar counts from periodic tightness and exact/ordinary coverage: active counts are three and five at successive vertices despite the correct global average four. This is an uncoloured class-model counterexample, not an actual equivalence cover or a counterexample to OP-205.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem cycle_power_dyadic_periodic_count_variation_counterexample :
    ∃ b : ZMod 16 → ℕ → Bool,
      (∀ p, cycle_power_dyadic_class_weight 3 (b p) =
        (range 8).sum (fun a => (b p a).toNat)) ∧
      (∀ (j : Fin 3) (v : ZMod 16), (range (2^(j : ℕ))).sum (fun a =>
        (b (v-(a : ZMod 16)) a && b (v-(a : ZMod 16)) (a+8-2^(j : ℕ))).toNat) = 1) ∧
      (∀ (d : Fin 7) (v : ZMod 16), ∃ a ∈ range (8-((d : ℕ)+1)),
        b (v-(a : ZMod 16)) a = true ∧
        b (v-(a : ZMod 16)) (a+((d : ℕ)+1)) = true) ∧
      (Finset.univ : Finset (ZMod 16)).sum (fun v =>
        (range 8).sum (fun a => (b (v-(a : ZMod 16)) a).toNat)) = 64 ∧
      (range 8).sum (fun a => (b (0-(a : ZMod 16)) a).toNat) = 3 ∧
      (range 8).sum (fun a => (b (1-(a : ZMod 16)) a).toNat) = 5 := by
  let b : ZMod 16 → ℕ → Bool := fun p a => decide (a ∈
    (match p.val with
    | 0 => {0, 7}
    | 1 => {0, 6, 7}
    | 2 => {0, 1, 5, 6, 7}
    | 3 => {0, 7}
    | 4 => {0, 1, 2, 3, 4, 5, 6, 7}
    | 5 => {0, 7}
    | 6 => {0, 6, 7}
    | 7 => {0, 1, 5, 6, 7}
    | 8 => {0, 7}
    | 9 => {0, 1, 2, 3, 4, 5, 6, 7}
    | 10 => {0, 7}
    | 11 => {0, 6, 7}
    | 12 => {0, 1, 2, 5, 6, 7}
    | 13 => {0, 7}
    | 14 => {0, 6, 7}
    | 15 => {0, 1, 2, 3, 4, 5, 6, 7}
    | _ => {0, 7} : Finset ℕ))
  refine ⟨b, ?_⟩
  decide
