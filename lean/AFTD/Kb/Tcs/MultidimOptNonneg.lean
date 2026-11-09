import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance
import AFTD.Kb.Tcs.MultidimOpt
import AFTD.Kb.Tcs.MultidimIsFeasibleSchedule

/-!
# multidim_opt_nonneg

Topic: online_algorithms   Node: 02a2abc2c5ee

Provenance: helper lemma. folklore

The offline optimal total completion time multidim_opt I of any multidimensional scheduling instance I with D resources is non-negative.
-/

/-- The offline optimal total completion time of a multidimensional scheduling instance is non-negative. -/
theorem multidim_opt_nonneg {D : ℕ} (I : MultidimInstance D) : 0 ≤ multidim_opt I := by
  dsimp [multidim_opt]
  have h_nonneg : ∀ s ∈ { s | ∃ (x : Fin I.n → ℝ → ℝ) (C : Fin I.n → ℝ), multidim_is_feasible_schedule I x C ∧ s = ∑ j, C j }, 0 ≤ s := by
    intro s hs
    rcases hs with ⟨x, C, h_feas, rfl⟩
    rcases h_feas with ⟨-, -, hC⟩
    apply Finset.sum_nonneg
    intro j _
    exact (hC j).1
  by_cases hS : { s | ∃ (x : Fin I.n → ℝ → ℝ) (C : Fin I.n → ℝ), multidim_is_feasible_schedule I x C ∧ s = ∑ j, C j }.Nonempty
  · exact le_csInf hS h_nonneg
  · have : { s | ∃ (x : Fin I.n → ℝ → ℝ) (C : Fin I.n → ℝ), multidim_is_feasible_schedule I x C ∧ s = ∑ j, C j } = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hS
    rw [this, Real.sInf_empty]
