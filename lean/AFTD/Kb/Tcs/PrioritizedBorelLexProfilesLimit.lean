import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelLexProfilesPrefixStabilize
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# prioritized_borel_lex_profiles_limit

Topic: automata   Node: d99bced0cd6f

Provenance: helper lemma. arXiv:2611.10136, Section 5.2.2; lexicographic priority profiles

A lexicographically nondecreasing sequence of infinite binary profiles has a coordinatewise limit, with uniform eventual agreement on each finite prefix.
-/

theorem prioritized_borel_lex_profiles_limit (profiles : ℕ → ℕ → Bool)
    (hmono : Monotone (fun n => toLex (profiles n))) :
    ∃ limit : ℕ → Bool, ∀ k, ∃ N, ∀ n ≥ N, ∀ i < k, profiles n i = limit i := by
  classical
  choose N hN using prioritized_borel_lex_profiles_prefix_stabilize profiles hmono
  let limit : ℕ → Bool := fun i => profiles (N (i+1)) i
  refine ⟨limit, ?_⟩
  intro k
  refine ⟨N k, ?_⟩
  intro n hn i hi
  have hfirst := hN k n hn i hi
  let j := max (N k) (N (i+1))
  have hleft := hN k j (le_max_left _ _) i hi
  have hright := hN (i+1) j (le_max_right _ _) i (by omega)
  dsimp [limit]
  exact hfirst.trans (hleft.symm.trans hright)
