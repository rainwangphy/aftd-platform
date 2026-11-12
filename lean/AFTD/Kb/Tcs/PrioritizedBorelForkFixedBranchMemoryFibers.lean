import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkValid
import AFTD.Kb.Tcs.PrioritizedBorelForkOneBranchMemoryFibers

/-!
# prioritized_borel_fork_fixed_branch_memory_fibers

Topic: automata   Node: ca2d4a434022

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

For any finite-memory assignment, one infinite visible sequence and one fixed memory value have arbitrarily large compatible hidden-history fibers along its prefixes.
-/

theorem prioritized_borel_fork_fixed_branch_memory_fibers {M : Type} [Fintype M]
    (color : List Bool → List Bool → Bool) (mem : List Bool → List Bool → M) :
    ∃ f : ℕ → Bool, ∃ m : M, ∀ d, ∃ n, ∃ S : Finset (List Bool),
      d < S.card ∧ ∀ h ∈ S,
        PrioritizedBorelForkValid color (List.ofFn (fun i : Fin n => f i)) h ∧
        mem (List.ofFn (fun i : Fin n => f i)) h = m := by
  classical
  obtain ⟨f, hf⟩ := prioritized_borel_fork_one_branch_memory_fibers color mem
  choose n m S hsize hvalid using hf
  have hall : ∃ᶠ d : ℕ in Filter.atTop, ∃ x : M, m d = x := by
    exact (Filter.Eventually.of_forall fun d => ⟨m d, rfl⟩).frequently
  obtain ⟨m0, hm0⟩ := Filter.frequently_exists.mp hall
  refine ⟨f, m0, ?_⟩
  intro d
  obtain ⟨j, hj, hjm⟩ := Filter.frequently_atTop.mp hm0 d
  refine ⟨n j, S j, lt_of_le_of_lt hj (hsize j), ?_⟩
  intro h hh
  obtain ⟨hv, hmem⟩ := hvalid j h hh
  exact ⟨hv, hmem.trans hjm⟩
