import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_whole_class_fractional_counterexample

Topic: combinatorics   Node: c8b314387f8c

Provenance: helper lemma. Exact fractional witness for the local-configuration relaxation in OP-205 / RT-1, experiment6403, following arXiv:2610.15635. This is an integrality barrier for a proposed proof route, not a Boolean model, an equivalence cover, or a counterexample to the main conjecture. No research advance claimed.

Five genuine tight radius-eight class shapes, with positive integer multiplicities totaling twelve, satisfy all dyadic exact-edge and ordinary coverage conditions in expectation and have expected class size four, yet boundary mismatch has total weight four. Thus exact single-class shape distributions alone do not force pairing.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem cycle_power_dyadic_whole_class_fractional_counterexample :
    ∃ (b : Fin 5 → ℕ → Bool) (w : Fin 5 → ℕ),
      (∑ i, w i) = 12 ∧
      (∀ i, b i 0 = true ∧ b i 7 = true) ∧
      (∀ i, cycle_power_dyadic_class_weight 3 (b i) =
        (range 8).sum (fun a => (b i a).toNat)) ∧
      (∑ i, w i * (range 8).sum (fun a => (b i a).toNat)) = 48 ∧
      (∀ j : Fin 3, (∑ i, w i * (range (2 ^ (j : ℕ))).sum (fun a =>
        (b i a && b i (a + 8 - 2 ^ (j : ℕ))).toNat)) = 12) ∧
      (∀ d : Fin 7, 12 ≤ ∑ i, w i * (range (8 - ((d : ℕ) + 1))).sum (fun a =>
        (b i a && b i (a + ((d : ℕ) + 1))).toNat)) ∧
      (∑ i, w i * (Bool.xor (b i 1) (b i 6)).toNat) = 4 := by
  let b : Fin 5 → ℕ → Bool := fun i a => decide (a ∈
    match i.val with
    | 0 => ({0, 7} : Finset ℕ)
    | 1 => {0, 1, 7}
    | 2 => {0, 1, 4, 7}
    | 3 => {0, 1, 2, 5, 6, 7}
    | _ => range 8)
  let w : Fin 5 → ℕ := fun i =>
    match i.val with
    | 0 => 4
    | 1 => 2
    | 2 => 2
    | 3 => 3
    | _ => 1
  refine ⟨b, w, ?_⟩
  decide
