import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkValid
import AFTD.Kb.Tcs.PrioritizedBorelForkOneInfiniteBranch

/-!
# prioritized_borel_fork_one_branch_memory_fibers

Topic: automata   Node: bdba0f81a166

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

For any finite-memory assignment, one infinite visible sequence has prefixes with arbitrarily large compatible hidden-history fibers at some memory value.
-/

theorem prioritized_borel_fork_one_branch_memory_fibers {M : Type} [Fintype M]
    (color : List Bool → List Bool → Bool) (mem : List Bool → List Bool → M) :
    ∃ f : ℕ → Bool, ∀ d, ∃ n, ∃ m : M, ∃ S : Finset (List Bool),
      d < S.card ∧ ∀ h ∈ S,
        PrioritizedBorelForkValid color (List.ofFn (fun i : Fin n => f i)) h ∧
        mem (List.ofFn (fun i : Fin n => f i)) h = m := by
  classical
  obtain ⟨f, hf⟩ := prioritized_borel_fork_one_infinite_branch color
  refine ⟨f, ?_⟩
  intro d
  let n := Fintype.card M * d
  let u : List Bool := List.ofFn (fun i : Fin n => f i)
  obtain ⟨T, hsize, hvalid⟩ := hf n
  have hlarge : (Finset.univ : Finset M).card * d < T.card := by
    simp only [Finset.card_univ]
    dsimp [n] at hsize
    omega
  obtain ⟨m, _, hm⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := T) (t := Finset.univ) (f := mem u) (n := d)
    (by simp) hlarge
  refine ⟨n, m, T.filter (fun h => mem u h = m), hm, ?_⟩
  intro h hh
  obtain ⟨hhT, hhm⟩ := Finset.mem_filter.mp hh
  exact ⟨hvalid h hhT, hhm⟩
