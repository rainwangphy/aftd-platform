import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AllocationBundle
import AFTD.Kb.GameTheoryEconomics.AllocationIsEnvyFreeable

/-!
# two_agent_envy_freeable_iff

Topic: fair_division   Node: fe8a85e58ec4

Provenance: helper lemma. arXiv:2610.14994, Theorem 2.1 (specialized to n=2)

For two agents with arbitrary valuations over bundles of items, an allocation is envy-freeable if and only if the sum of agent 0's net value for bundle 0 over bundle 1 and agent 1's net value for bundle 1 over bundle 0 is non-negative.
-/

/-- Characterization of envy-freeability for two agents: an allocation is envy-freeable if and only if the sum of pairwise negative envies is non-negative. -/
theorem two_agent_envy_freeable_iff
    {M : Type*} [Fintype M]
    (v : Fin 2 → Finset M → ℝ) (A : M → Fin 2) :
    allocation_is_envy_freeable v A ↔
      0 ≤ (v 0 (allocation_bundle A 0) - v 0 (allocation_bundle A 1)) +
          (v 1 (allocation_bundle A 1) - v 1 (allocation_bundle A 0)) := by
  constructor
  · rintro ⟨p, hp_nonneg, hp_ef⟩
    have h01 := hp_ef 0 1
    have h10 := hp_ef 1 0
    linarith
  · intro h
    let x := v 0 (allocation_bundle A 0) - v 0 (allocation_bundle A 1)
    rcases le_total 0 x with hx | hx
    · use ![0, x]
      constructor
      · intro i
        fin_cases i <;> simp [hx]
      · intro i j
        fin_cases i <;> fin_cases j <;> (simp; try linarith)
    · use ![-x, 0]
      constructor
      · intro i
        fin_cases i <;> (simp; try linarith)
      · intro i j
        fin_cases i <;> fin_cases j <;> (simp; try linarith)
