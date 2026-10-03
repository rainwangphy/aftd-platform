import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsOrientation
import AFTD.Kb.GameTheoryEconomics.IsGraphValuation
import AFTD.Kb.GameTheoryEconomics.IsMonotoneValuation
import AFTD.Kb.GameTheoryEconomics.HasMaxMarginalOne
import AFTD.Kb.GameTheoryEconomics.IsEnvyFreeWithSubsidy
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# multigraph_orientation_subsidy_four_agents

Topic: fair_division   Node: 8e0e7468224e

There is a four-agent multigraph with monotone graph valuations, normalised so the largest marginal is 1, in which every envy-free orientation needs a total subsidy of at least 13/5, and 13/5 suffices. Edges e0, e1 are parallel between agents 0 and 1, edge e2 joins agents 2 and 3. Agent 0 values e0, e1 at 1 each additively; agent 1 values one of them at 1/5 and both at 6/5; agents 2 and 3 value e2 at 1. This beats the lower bound n - 2 = 2 of arXiv:2502.13671 (Example 20) at n = 4.
-/

/-- The four-agent instance: edges 0 and 1 are parallel, joining agents 0 and 1; edge 2 joins
agents 2 and 3. -/
def subsidy_four_ends : Fin 3 → Fin 4 × Fin 4 := ![(0, 1), (0, 1), (2, 3)]

/-- Agent 0 values edges 0 and 1 at 1 each (additively); agent 1 values one of them at 1/5 and
both at 6/5; agents 2 and 3 value edge 2 at 1. -/
noncomputable def subsidy_four_val : Fin 4 → Finset (Fin 3) → ℝ
  | 0, S => (if 0 ∈ S then 1 else 0) + (if 1 ∈ S then 1 else 0)
  | 1, S => if 0 ∈ S ∧ 1 ∈ S then 6 / 5 else if 0 ∈ S ∨ 1 ∈ S then 1 / 5 else 0
  | 2, S => if 2 ∈ S then 1 else 0
  | 3, S => if 2 ∈ S then 1 else 0

lemma subsidy_four_graph : is_graph_valuation subsidy_four_ends subsidy_four_val := by
  intro i S
  have hx : ∀ x, x ∈ S.filter (fun e => (subsidy_four_ends e).1 = i ∨ (subsidy_four_ends e).2 = i)
      ↔ x ∈ S ∧ ((subsidy_four_ends x).1 = i ∨ (subsidy_four_ends x).2 = i) :=
    fun x => Finset.mem_filter
  fin_cases i <;> simp only [subsidy_four_val] <;> simp only [hx] <;>
    simp (config := { decide := true }) [subsidy_four_ends]

lemma subsidy_four_monotone (i : Fin 4) : is_monotone_valuation (subsidy_four_val i) := by
  refine ⟨by fin_cases i <;> simp [subsidy_four_val], fun S T hST => ?_⟩
  have h0 := @hST 0; have h1 := @hST 1; have h2 := @hST 2
  fin_cases i <;> simp only [subsidy_four_val] <;>
    by_cases a0 : (0 : Fin 3) ∈ S <;> by_cases a1 : (1 : Fin 3) ∈ S <;>
    by_cases a2 : (2 : Fin 3) ∈ S <;> by_cases b0 : (0 : Fin 3) ∈ T <;>
    by_cases b1 : (1 : Fin 3) ∈ T <;> by_cases b2 : (2 : Fin 3) ∈ T <;>
    simp_all <;> norm_num

lemma subsidy_four_marginal (i : Fin 4) : has_max_marginal_one (subsidy_four_val i) := by
  refine ⟨fun S e => ?_, ?_⟩
  · fin_cases i <;> fin_cases e <;> simp only [subsidy_four_val] <;>
      by_cases a0 : (0 : Fin 3) ∈ S <;> by_cases a1 : (1 : Fin 3) ∈ S <;>
      by_cases a2 : (2 : Fin 3) ∈ S <;> simp [a0, a1, a2] <;> norm_num
  · fin_cases i
    · exact ⟨∅, 0, by simp [subsidy_four_val]⟩
    · exact ⟨{0}, 1, by simp [subsidy_four_val]; norm_num⟩
    · exact ⟨∅, 2, by simp [subsidy_four_val]⟩
    · exact ⟨∅, 2, by simp [subsidy_four_val]⟩

lemma subsidy_four_lower (σ : Fin 3 → Fin 4) (p : Fin 4 → ℝ)
    (hσ : is_orientation subsidy_four_ends σ)
    (hef : is_envy_free_with_subsidy subsidy_four_val σ p) : 13 / 5 ≤ ∑ i, p i := by
  obtain ⟨hp, h⟩ := hef
  have e0 := hσ 0; have e1 := hσ 1; have e2 := hσ 2
  simp only [subsidy_four_ends, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
  have mem : ∀ x j, x ∈ bundle_of σ j ↔ σ x = j := by
    intro x j; simp [bundle_of]
  have h01 := h 0 1; have h02 := h 0 2; have h03 := h 0 3
  have h10 := h 1 0; have h12 := h 1 2; have h13 := h 1 3
  have h20 := h 2 0; have h21 := h 2 1; have h23 := h 2 3
  have h30 := h 3 0; have h31 := h 3 1; have h32 := h 3 2
  simp only [subsidy_four_val, mem] at h01 h02 h03 h10 h12 h13 h20 h21 h23 h30 h31 h32
  have p0 := hp 0; have p1 := hp 1; have p2 := hp 2; have p3 := hp 3
  simp only [Fin.sum_univ_four]
  rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;>
    simp only [e0, e1, e2] at h01 h02 h03 h10 h12 h13 h20 h21 h23 h30 h31 h32 <;>
    simp (config := { decide := true }) only [ite_true, ite_false,
      or_false, false_or, true_and, and_true, true_or, or_true]
      at h01 h02 h03 h10 h12 h13 h20 h21 h23 h30 h31 h32 <;>
    norm_num at h01 h02 h03 h10 h12 h13 h20 h21 h23 h30 h31 h32 <;>
    linarith

lemma subsidy_four_attained :
    is_orientation subsidy_four_ends ![0, 1, 2] ∧
      is_envy_free_with_subsidy subsidy_four_val ![0, 1, 2] ![4 / 5, 4 / 5, 0, 1] := by
  refine ⟨fun e => ?_, fun i => ?_, fun i j => ?_⟩
  · fin_cases e <;> decide
  · fin_cases i <;> simp <;> norm_num
  · have mem : ∀ x j, x ∈ bundle_of (![0, 1, 2] : Fin 3 → Fin 4) j ↔
        (![0, 1, 2] : Fin 3 → Fin 4) x = j := by
      intro x j; simp [bundle_of]
    fin_cases i <;> fin_cases j <;> simp [subsidy_four_val, mem] <;> norm_num

theorem multigraph_orientation_subsidy_four_agents :
    ∃ (ends : Fin 3 → Fin 4 × Fin 4) (v : Fin 4 → Finset (Fin 3) → ℝ),
      (∀ e, (ends e).1 ≠ (ends e).2) ∧ is_graph_valuation ends v ∧
      (∀ i, is_monotone_valuation (v i) ∧ has_max_marginal_one (v i)) ∧
      (∀ σ p, is_orientation ends σ → is_envy_free_with_subsidy v σ p → 13 / 5 ≤ ∑ i, p i) ∧
      ∃ σ p, is_orientation ends σ ∧ is_envy_free_with_subsidy v σ p ∧ ∑ i, p i = 13 / 5 := by
  refine ⟨subsidy_four_ends, subsidy_four_val, fun e => ?_, subsidy_four_graph,
    fun i => ⟨subsidy_four_monotone i, subsidy_four_marginal i⟩, subsidy_four_lower,
    ![0, 1, 2], ![4 / 5, 4 / 5, 0, 1], subsidy_four_attained.1, subsidy_four_attained.2, ?_⟩
  · fin_cases e <;> decide
  · simp [Fin.sum_univ_four]; norm_num
