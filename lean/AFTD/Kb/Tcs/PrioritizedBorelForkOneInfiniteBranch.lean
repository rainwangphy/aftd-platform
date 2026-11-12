import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkValid
import AFTD.Kb.Tcs.PrioritizedBorelFiniteHistoryShadow
import AFTD.Kb.Tcs.PrioritizedBorelForkPrefixChain

/-!
# prioritized_borel_fork_one_infinite_branch

Topic: automata   Node: d0db52df937d

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

For every history-dependent fork response, one infinite visible block sequence has prefixes with arbitrarily many compatible hidden histories.
-/

theorem prioritized_borel_fork_one_infinite_branch (color : List Bool → List Bool → Bool) :
    ∃ f : ℕ → Bool, ∀ n, ∃ S : Finset (List Bool), n+1 ≤ S.card ∧
      ∀ h ∈ S, PrioritizedBorelForkValid color (List.ofFn (fun i : Fin n => f i)) h := by
  classical
  let P : List Bool → Prop := fun u =>
    ∀ k ≤ u.length, ∃ S : Finset (List Bool), k+1 ≤ S.card ∧
      ∀ h ∈ S, PrioritizedBorelForkValid color (u.take k) h
  have hpref : ∀ xs ys, P (xs ++ ys) → P xs := by
    intro xs ys hx k hk
    obtain ⟨S, hs, hv⟩ := hx k (by simp; omega)
    refine ⟨S, hs, ?_⟩
    have heq : (xs ++ ys).take k = xs.take k := List.take_append_of_le_length hk
    simpa [heq] using hv
  have hdepth : ∀ n, ∃ u : List Bool, u.length = n ∧ P u := by
    intro n
    obtain ⟨u, hu, hc⟩ := prioritized_borel_fork_prefix_chain color n
    exact ⟨u, hu, by simpa [P, hu] using hc⟩
  obtain ⟨f, hf⟩ := prioritized_borel_finite_history_shadow Bool P hpref hdepth
  refine ⟨f, ?_⟩
  intro n
  have h := hf n
  obtain ⟨S, hs, hv⟩ := h n (by simp)
  refine ⟨S, hs, ?_⟩
  have htake : (List.ofFn (fun i : Fin n => f i)).take n =
      List.ofFn (fun i : Fin n => f i) := by
    simpa only [List.length_ofFn] using
      (List.take_length : (List.ofFn (fun i : Fin n => f i)).take
        (List.ofFn (fun i : Fin n => f i)).length = List.ofFn (fun i : Fin n => f i))
  rw [htake] at hv
  exact hv
