import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_sixteen_block_vertical_average_barrier

Topic: combinatorics   Node: 617e57fbb8fb

Provenance: helper lemma. Uniform-route audit for OP-205 / RT-1, following arXiv:2610.15635. Experiment8260 finds this independent-class mixture. This refutes only the averaged zero-vertical-density shortcut, not an integer rooted model or graph covering claim.

Eight tight radius16 dyadic profiles with positive integer weights totaling60 satisfy optimal mean size5, all exact dyadic pair averages, every ordinary pair-coverage average, and monotone outer eighths; the weighted upper-vertical defect at offsets1/3 nevertheless has mass8. Thus zero upper-vertical density does not follow from these single-class average constraints.
-/

theorem cycle_power_sixteen_block_vertical_average_barrier :
    ∃ (b : Fin 8 → ℕ → Bool) (w : Fin 8 → ℕ),
      (∑ i, w i) = 60 ∧
      (∀ i, 0 < w i) ∧
      (∀ i, b i 0 = true ∧ b i 15 = true) ∧
      (∀ i, cycle_power_dyadic_class_weight 4 (b i) =
        (Finset.range 16).sum (fun a => (b i a).toNat)) ∧
      (∀ i, (∀ a c : Fin 2, a ≤ c → b i c = true → b i a = true) ∧
        (∀ a c : Fin 16, 14 ≤ (a : ℕ) → a ≤ c → b i a = true → b i c = true)) ∧
      (∑ i, w i * (Finset.range 16).sum (fun a => (b i a).toNat)) = 300 ∧
      (∀ j : Fin 4, (∑ i, w i * (Finset.range (2^(j : ℕ))).sum
        (fun a => (b i a && b i (a+16-2^(j : ℕ))).toNat)) = 60) ∧
      (∀ d : Fin 15, 60 ≤ ∑ i, w i * (Finset.range (16-((d : ℕ)+1))).sum
        (fun a => (b i a && b i (a+((d : ℕ)+1))).toNat)) ∧
      (∑ i, w i * (b i 3 && !(b i 1)).toNat) = 8 := by
  let masks : Fin 8 → ℕ := ![32769,32777,49155,49161,57351,57735,64575,65151]
  let b : Fin 8 → ℕ → Bool := fun i a => (masks i).testBit a
  let w : Fin 8 → ℕ := ![24,4,12,4,1,5,5,5]
  refine ⟨b,w,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide
