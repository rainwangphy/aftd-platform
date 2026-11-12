import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkValid
import AFTD.Kb.Tcs.PrioritizedBorelForkExponentialHistories

/-!
# prioritized_borel_fork_memory_fiber_unbounded

Topic: automata   Node: 8fff296631b9

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2, smallest lower-bound arena; three-move fork obstruction

For every history-dependent response and every finite-memory assignment, arbitrarily many compatible hidden histories can reach one common visible node and one memory value.
-/

theorem prioritized_borel_fork_memory_fiber_unbounded {M : Type} [Fintype M]
    (color : List Bool → List Bool → Bool) (mem : List Bool → List Bool → M)
    (d : ℕ) : ∃ u : List Bool, ∃ m : M, ∃ S : Finset (List Bool),
      d < S.card ∧ ∀ h ∈ S, PrioritizedBorelForkValid color u h ∧ mem u h = m := by
  classical
  let n := Fintype.card M * d
  obtain ⟨u, T, _, hsize, _, hvalid⟩ := prioritized_borel_fork_exponential_histories color n
  have hlarge : (Finset.univ : Finset M).card * d < T.card := by
    simp only [Finset.card_univ]
    dsimp [n] at hsize
    omega
  obtain ⟨m, _, hm⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := T) (t := Finset.univ) (f := mem u) (n := d)
    (by simp) hlarge
  refine ⟨u, m, T.filter (fun h => mem u h = m), hm, ?_⟩
  intro h hh
  obtain ⟨hhT, hhm⟩ := Finset.mem_filter.mp hh
  exact ⟨hvalid h hhT, hhm⟩
