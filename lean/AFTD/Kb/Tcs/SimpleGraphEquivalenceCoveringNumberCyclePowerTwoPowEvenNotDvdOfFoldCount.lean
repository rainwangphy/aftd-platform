import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicFoldStructStep
import AFTD.Kb.Tcs.CyclePowerFifteenModelAlternatingEndpoint
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerTwoPowEvenNotDvdOfAlternatingEndpoint
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# simple_graph_equivalence_covering_number_cycle_power_two_pow_even_not_dvd_of_fold_count

Topic: combinatorics   Node: 72f86dad558b

Provenance: helper lemma. RT-1 / OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Session 2026-11-09: folding offsets modulo 2^t (experiment 19407).

Conditional reduction of OP-205 to a single count identity plus a middle-bit lemma: if for every t ≥ 4 every model at exponent t+1 has 2^t-periodic left count, and classes without bit 1 lack the two middle bits 2^t-1, 2^t (when bit 1 alternates and the other inner bits of such classes vanish), then eq(C_n^k) = m+2 for k+1 = 2^m, n even, n ≥ max(2k+2, k²(k+2)), (k+1) not dividing n. Replaces the alternation hypothesis of ..._of_alternating_endpoint.
-/

theorem simple_graph_equivalence_covering_number_cycle_power_two_pow_even_not_dvd_of_fold_count
    (hfold : ∀ t : ℕ, 4 ≤ t → ∀ (x : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight (t+1) (x p) =
        (Finset.range (2^(t+1))).sum (fun a => (x p a).toNat)) →
      (∀ j < t+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^j)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^(t+1) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(t+1)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^(t+1))).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = (t+1)+1) →
      ∀ v : ℤ, (Finset.range (2^t)).sum (fun a => (x (v-(a : ℤ)) a).toNat) =
        (Finset.range (2^t)).sum (fun a => (x (v+(2:ℤ)^t-(a : ℤ)) a).toNat))
    (hmid : ∀ t : ℕ, 4 ≤ t → ∀ (x : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight (t+1) (x p) =
        (Finset.range (2^(t+1))).sum (fun a => (x p a).toNat)) →
      (∀ j < t+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^j)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^(t+1) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(t+1)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^(t+1))).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = (t+1)+1) →
      (∀ p : ℤ, x (p+1) 1 = !x p 1) →
      (∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(t+1) - 1 → j ≠ 2^t - 1 → j ≠ 2^t →
        x p j = false) →
      ∀ p : ℤ, x p 1 = false → x p (2^t - 1) = false ∧ x p (2^t) = false)
    (k m n : ℕ) (hm : 1 ≤ m) (hkm : k + 1 = 2 ^ m)
    (hn : max (2 * k + 2) (k ^ 2 * (k + 2)) ≤ n) (hev : Even n) (hnd : ¬ (k + 1) ∣ n) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n k) = m + 2 := by
  have key : ∀ t : ℕ, 4 ≤ t → ∀ (x : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight t (x p) =
        (Finset.range (2^t)).sum (fun a => (x p a).toNat)) →
      (∀ j < t, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^t-2^j)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^t → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^t-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^t)).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = t+1) →
      (∀ p : ℤ, x (p+1) 1 = !x p 1) ∧
      (∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^t - 1 → x p j = false) := by
    intro t ht4
    induction t, ht4 using Nat.le_induction with
    | base => exact cycle_power_fifteen_model_alternating_endpoint
    | succ t ht4 ih =>
      intro x htight hexact hcover hcount
      exact cycle_power_dyadic_fold_struct_step t (by omega) ih x htight hexact hcover hcount
        (hfold t ht4 x htight hexact hcover hcount)
        (hmid t ht4 x htight hexact hcover hcount)
  refine simple_graph_equivalence_covering_number_cycle_power_two_pow_even_not_dvd_of_alternating_endpoint ?_ k m n hm hkm hn hev hnd
  intro t ht x h1 h2 h3 h4
  exact key t (by omega) x h1 h2 h3 h4
