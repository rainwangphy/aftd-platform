import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CyclicTwoOrientation
import AFTD.Kb.GameTheoryEconomics.IsOrientation
import AFTD.Kb.GameTheoryEconomics.IsPropmOrientation
import AFTD.Kb.GameTheoryEconomics.PropmCyclicTwoOrientation
import AFTD.Kb.GameTheoryEconomics.PropmOrientationOfOutDegreeTwo

/-!
# propm_orientation_exists_of_le_five

Topic: fair_division   Node: 0f316fe7f230

Every loopless multigraph on at most five agents with nonnegative additive valuations admits a PROPm orientation (with the PROPm slack taken over relevant items).
-/

/-- Every loopless multigraph on at most five agents with nonnegative additive valuations admits a PROPm orientation. -/
theorem propm_orientation_exists_of_le_five {m n : ℕ} (hn : n ≤ 5)
    (ends : Fin m → Fin n × Fin n) (hloop : ∀ e, (ends e).1 ≠ (ends e).2)
    (u : Fin n → Fin m → ℝ) (hu : ∀ i e, 0 ≤ u i e) :
    ∃ σ, is_orientation ends σ ∧ is_propm_orientation ends u σ := by
  obtain ⟨hcov, hdeg⟩ := propm_cyclic_two_orientation n hn
  exact propm_orientation_of_out_degree_two ends hloop u hu
    ⟨cyclic_two_orientation n, fun e => hcov _ _ (hloop e), hdeg⟩
