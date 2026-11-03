import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGreedyRawMoment
import AFTD.Kb.Tcs.CycleGapMerge
import AFTD.Kb.Tcs.CycleGreedyMomentsAllFuel

/-!
# cycle_greedy_raw_moment_zero

Topic: online_algorithms   Node: 79dfe63985ca

Provenance: helper lemma. arXiv:2610.15776

The zeroth raw moment of the greedy online assignment cost on an n-cycle is identically 1 for all n ≥ 2.
-/

lemma cycle_greedy_raw_moment_zero_fuel (fuel n : ℕ) (hfuel : 1 ≤ fuel) (g : List ℕ) :
    cycle_greedy_moments_all_fuel fuel 0 n g = [1] := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  rcases f with _ | f
  · simp [cycle_greedy_moments_all_fuel]
  · rw [cycle_greedy_moments_all_fuel.eq_3 0 n g (f + 1) (by simp)]
    split_ifs with h
    · simp
    · change List.foldl (fun acc i => [1]) [1] (List.range g.length) = [1]
      generalize List.range g.length = l
      induction l with
      | nil => rfl
      | cons x xs ih => exact ih

/-- The zeroth raw moment of greedy assignment cost on an n-cycle is identically 1 for all n ≥ 2. -/
theorem cycle_greedy_raw_moment_zero (n : ℕ) (hn : 2 ≤ n) : cycle_greedy_raw_moment 0 n = 1 := by
  unfold cycle_greedy_raw_moment
  rw [cycle_greedy_raw_moment_zero_fuel n n (by omega)]
  rfl
