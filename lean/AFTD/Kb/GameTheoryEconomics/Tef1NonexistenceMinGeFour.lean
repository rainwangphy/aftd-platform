import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsTef1
import AFTD.Kb.GameTheoryEconomics.Tef1ExistsLeThreeChoresThreeAgents

/-!
# tef1_nonexistence_min_ge_four

Topic: fair_division   Node: d635af44f430

Provenance: helper lemma. arXiv:2611.25892 Sec. 7

If m : ℕ is the least element (IsLeast) of the set of natural numbers k for which there exists a 3-agent, k-chore instance with nonnegative additive costs admitting no TEF1 allocation (∃ (d : Fin 3 → Fin k → ℝ), (∀ i c, 0 ≤ d i c) ∧ ∀ π, ¬ is_tef1 3 k d π), then 4 ≤ m.
-/

/-- Any instance admitting no TEF1 allocation with three agents has at least four chores. -/
theorem tef1_nonexistence_min_ge_four (m : ℕ)
    (hm : IsLeast {k : ℕ | ∃ (d : Fin 3 → Fin k → ℝ), (∀ i c, 0 ≤ d i c) ∧ ∀ π, ¬ is_tef1 3 k d π} m) :
    4 ≤ m := by
  by_contra! h
  obtain ⟨d, hd, hno⟩ := hm.1
  obtain ⟨π, hπ⟩ := tef1_exists_le_three_chores_three_agents m (by omega) d hd
  exact hno π hπ
