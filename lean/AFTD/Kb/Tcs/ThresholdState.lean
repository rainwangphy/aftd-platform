import AFTD.Prelude

/-!
# threshold_state

Topic: online_algorithms   Node: 6febffdc9842

Provenance: formalization of a published result. Source: arXiv:2611.06955, Definition 5

Given horizon T : ℕ, increments a : Fin (T - 1) → NNReal, and reset price K : ℝ, threshold_state T a K : Fin T → NNReal × NNReal is defined recursively: at index ⟨0, _⟩ it is (0, 0), and at index ⟨t + 1, _⟩, letting (h, acc) = threshold_state T a K ⟨t, _⟩, it is (a ⟨t, _⟩, 0) if K ≤ (acc : ℝ) + (h : ℝ), and (h + a ⟨t, _⟩, acc + h) otherwise.
-/

/-- The state (history, accumulator) of the threshold rule before each call. -/
noncomputable def threshold_state (T : ℕ) (a : Fin (T - 1) → NNReal) (K : ℝ) : Fin T → NNReal × NNReal
  | ⟨0, _⟩ => (0, 0)
  | ⟨t + 1, ht⟩ =>
    let (h, acc) := threshold_state T a K ⟨t, by omega⟩
    have ht_lt : t < T - 1 := by omega
    if K ≤ (acc : ℝ) + (h : ℝ) then
      (a ⟨t, ht_lt⟩, 0)
    else
      (h + a ⟨t, ht_lt⟩, acc + h)
termination_by t => t.val
