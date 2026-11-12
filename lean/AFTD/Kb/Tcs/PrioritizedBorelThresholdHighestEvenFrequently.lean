import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelHighestRecurrentIndex
import AFTD.Kb.Tcs.PrioritizedBorelThresholdMaximumEvenFrequently

/-!
# prioritized_borel_threshold_highest_even_frequently

Topic: automata   Node: 3a677d0b7bac

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2, Proposition 41; threshold controller for the lower-bound example

For any positive bounded input sequence and threshold-memory update, the largest recurrent input occurs arbitrarily late when memory is smaller, and no larger input occurs after some point.
-/

theorem prioritized_borel_threshold_highest_even_frequently (s : ℕ) (f m : ℕ → ℕ)
    (hf : ∀ n, 1 ≤ f n ∧ f n ≤ s)
    (hstep : ∀ n, m (n+1) = if m n < f n then f n else 0) :
    ∃ I, 0 < I ∧ I ≤ s ∧ (∀ N, ∃ n ≥ N, f n = I) ∧
      (∃ N0, ∀ n, N0 ≤ n → f n ≤ I) ∧
      (∀ K, ∃ n ≥ K, f n = I ∧ m n < I) := by
  obtain ⟨I, hIpos, hIbound, hIrec, N0, hmax⟩ := prioritized_borel_highest_recurrent_index s f hf
  exact ⟨I, hIpos, hIbound, hIrec, ⟨N0, hmax⟩,
    prioritized_borel_threshold_maximum_even_frequently f m I N0 hIpos hmax hIrec hstep⟩
