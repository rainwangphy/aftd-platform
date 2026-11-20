import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsTef1
import AFTD.Kb.GameTheoryEconomics.Tef1NonexistenceNineChoresThreeAgents
import AFTD.Kb.GameTheoryEconomics.Tef1NonexistenceMinGeFour

/-!
# op_2102_min_chores_tef1_nonexistence_three_agents

Topic: fair_division   Node: f937a4458311

Provenance: formalization of a published result. Source: arXiv:2611.25892 Sec. 7

Open Problem OP-2102 (arXiv:2611.25892, Section 7): There exists a unique natural number m such that 4 ≤ m ∧ m ≤ 9 and m is the least element (IsLeast) of the set of all k : ℕ for which there exists a cost function d : Fin 3 → Fin k → ℝ with nonnegative costs admitting no TEF1 allocation (∀ π, ¬ is_tef1 3 k d π).
-/

/-- Open Problem OP-2102: The minimum number of chores for TEF1 nonexistence with three agents lies between 4 and 9. -/
theorem op_2102_min_chores_tef1_nonexistence_three_agents :
    ∃! m : ℕ, 4 ≤ m ∧ m ≤ 9 ∧
      IsLeast {k : ℕ | ∃ (d : Fin 3 → Fin k → ℝ), (∀ i c, 0 ≤ d i c) ∧ ∀ π, ¬ is_tef1 3 k d π} m := by
  have h9 : 9 ∈ {k : ℕ | ∃ (d : Fin 3 → Fin k → ℝ), (∀ i c, 0 ≤ d i c) ∧ ∀ π, ¬ is_tef1 3 k d π} :=
    tef1_nonexistence_nine_chores_three_agents
  have h_ex : ∃ n, n ∈ {k : ℕ | ∃ (d : Fin 3 → Fin k → ℝ), (∀ i c, 0 ≤ d i c) ∧ ∀ π, ¬ is_tef1 3 k d π} :=
    ⟨9, h9⟩
  classical
  let m := Nat.find h_ex
  have hm : IsLeast {k : ℕ | ∃ (d : Fin 3 → Fin k → ℝ), (∀ i c, 0 ≤ d i c) ∧ ∀ π, ¬ is_tef1 3 k d π} m :=
    ⟨Nat.find_spec h_ex, fun x hx => Nat.find_min' h_ex hx⟩
  have hm_ge : 4 ≤ m := tef1_nonexistence_min_ge_four m hm
  have hm_le : m ≤ 9 := hm.2 h9
  refine ⟨m, ⟨hm_ge, hm_le, hm⟩, ?_⟩
  intro y hy
  exact (hm.unique hy.2.2).symm
