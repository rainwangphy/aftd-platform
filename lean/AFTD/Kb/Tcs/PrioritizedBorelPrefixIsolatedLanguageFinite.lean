import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelCompactIsolatedPathsFinite
import AFTD.Kb.Tcs.PrioritizedBorelPrefixLanguageIsClosed

/-!
# prioritized_borel_prefix_isolated_language_finite

Topic: automata   Node: a86e203743be

Provenance: helper lemma. IN-829: compactness route to finite compatible plays.

For a compact discrete alphabet, the infinite sequences all of whose finite prefixes satisfy a given predicate form a finite set if each such sequence is uniquely determined by a finite prefix.
-/

theorem prioritized_borel_prefix_isolated_language_finite
    (A : Type*) [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A]
    (P : List A → Prop)
    (hisolate : ∀ f : ℕ → A, (∀ n, P (List.ofFn (fun i : Fin n => f i))) →
      ∃ n : ℕ, ∀ g : ℕ → A, (∀ m, P (List.ofFn (fun i : Fin m => g i))) →
        (∀ i < n, g i = f i) → g = f) :
    {f : ℕ → A | ∀ n : ℕ, P (List.ofFn (fun i : Fin n => f i))}.Finite := by
  apply prioritized_borel_compact_isolated_paths_finite A _ (prioritized_borel_prefix_language_isClosed A P)
  exact hisolate
