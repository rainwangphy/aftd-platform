import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelLexRestrictMonotone
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.PiLexFinite
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# prioritized_borel_lex_profiles_prefix_stabilize

Topic: automata   Node: a4c2ba600ffc

Provenance: helper lemma. arXiv:2611.10136, Section 5.2.2; lexicographic priority profiles

Every lexicographically nondecreasing sequence of infinite binary profiles eventually stabilizes on each finite prefix.
-/

theorem prioritized_borel_lex_profiles_prefix_stabilize (profiles : ℕ → ℕ → Bool)
    (hmono : Monotone (fun n => toLex (profiles n))) :
    ∀ k, ∃ N, ∀ n ≥ N, ∀ i < k, profiles n i = profiles N i := by
  classical
  intro k
  let f : ℕ → Lex (Fin k → Bool) := fun n => toLex (fun i => profiles n i)
  have hf : Monotone f := by
    intro a b hab
    exact prioritized_borel_lex_restrict_monotone k (profiles a) (profiles b) (hmono hab)
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition ⟨f, hf⟩
  refine ⟨N, ?_⟩
  intro n hn i hi
  have h := congrFun (congrArg ofLex (hN n hn)) (⟨i, hi⟩ : Fin k)
  simpa [f] using h.symm
