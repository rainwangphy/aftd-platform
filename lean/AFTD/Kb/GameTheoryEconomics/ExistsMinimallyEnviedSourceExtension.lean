import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExistsMinimallyEnviedSubset
import AFTD.Kb.GameTheoryEconomics.EnviedSubsetContainsAddedGood
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# exists_minimally_envied_source_extension

Topic: fair_division   Node: 41d4bbb1e029

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Standard minimal-envied-subset mechanism, arXiv:2002.05119v3 Observation 6 and Corollary 7; no novelty claim.

For nonnegative additive values and any family of finite bundles A, suppose A(s) is unenvied by every agent relative to her own A(i), and a good g outside A(s) has strictly positive value for s. Then A(s) union {g} contains a subset T containing g which some agent j strictly prefers to A(j), and deleting any good of T leaves value at most the own A(i) for every agent i.
-/

open Function Finset

theorem exists_minimally_envied_source_extension {m n : ℕ}
    (u : Fin n → Fin m → ℝ) (hu : ∀ i g, 0 ≤ u i g)
    (A : Fin n → Finset (Fin m)) (s : Fin n) (g : Fin m)
    (hg : g ∉ A s) (hpos : 0 < u s g)
    (hs : ∀ i, additive_valuation (u i) (A s) ≤ additive_valuation (u i) (A i)) :
    ∃ (j : Fin n) (T : Finset (Fin m)), T ⊆ insert g (A s) ∧ g ∈ T ∧
      additive_valuation (u j) (A j) < additive_valuation (u j) T ∧
      ∀ i, ∀ h ∈ T, additive_valuation (u i) (T.erase h) ≤
        additive_valuation (u i) (A i) := by
  classical
  have hex : ∃ i, additive_valuation (u i) (A i) <
      additive_valuation (u i) (insert g (A s)) := by
    refine ⟨s, ?_⟩
    simp only [additive_valuation, Finset.sum_insert hg]
    linarith
  obtain ⟨T, hT, henv, htrim⟩ := exists_minimally_envied_subset u
    (fun i => additive_valuation (u i) (A i)) (insert g (A s)) hex
  have hgT := envied_subset_contains_added_good u hu
    (fun i => additive_valuation (u i) (A i)) (A s) T g hT hs henv
  obtain ⟨j, hj⟩ := henv
  exact ⟨j, T, hT, hgT, hj, htrim⟩
