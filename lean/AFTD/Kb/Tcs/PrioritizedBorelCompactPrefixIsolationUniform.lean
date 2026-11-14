import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelCompactIsolatedPathsFinite

/-!
# prioritized_borel_compact_prefix_isolation_uniform

Topic: automata   Node: 004284cf2671

Provenance: helper lemma. IN-829: compactness route to a uniform choice cutoff.

If a closed set of paths over a compact discrete alphabet has each path determined by some finite prefix, then one common prefix length distinguishes all of its paths.
-/

theorem prioritized_borel_compact_prefix_isolation_uniform
    (A : Type*) [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A]
    (S : Set (ℕ → A)) (hclosed : IsClosed S)
    (hisolate : ∀ f ∈ S, ∃ n : ℕ, ∀ g ∈ S, (∀ i < n, g i = f i) → g = f) :
    ∃ N : ℕ, ∀ f ∈ S, ∀ g ∈ S, (∀ i < N, g i = f i) → g = f := by
  classical
  have hs := prioritized_borel_compact_isolated_paths_finite A S hclosed hisolate
  letI : Fintype S := hs.fintype
  let n : S → ℕ := fun f => Classical.choose (hisolate f f.property)
  let N : ℕ := Finset.univ.sup n
  refine ⟨N, ?_⟩
  intro f hf g hg hprefix
  let fs : S := ⟨f,hf⟩
  have hle : n fs ≤ N := Finset.le_sup (Finset.mem_univ fs)
  apply (Classical.choose_spec (hisolate f hf)) g hg
  intro i hi
  exact hprefix i (lt_of_lt_of_le hi hle)
