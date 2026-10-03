import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsOrientation
import AFTD.Kb.GameTheoryEconomics.IsGraphValuation
import AFTD.Kb.GameTheoryEconomics.IsMonotoneValuation
import AFTD.Kb.GameTheoryEconomics.HasMaxMarginalOne
import AFTD.Kb.GameTheoryEconomics.IsEnvyFreeWithSubsidy
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# multigraph_orientation_subsidy_three_halves

Topic: fair_division   Node: b751ec99ac48

There is a three-agent multigraph with monotone graph valuations, normalised so the largest marginal is 1, in which every envy-free orientation needs a total subsidy of at least 3/2, and 3/2 suffices. Edge b joins agents 0 and 1; edges c, d are parallel between agents 0 and 2. Agent 1 values b at 1; agent 2 values one of c, d at 1/2 and both at 3/2; agent 0 values b at 1, c and d at 1/4 each, any two edges at 5/4 and all three at 3/2. This beats the lower bound n - 2 = 1 of arXiv:2502.13671 (Example 20) at n = 3.
-/

/-- The three-agent gadget: edge 0 joins agents 0 and 1; edges 1 and 2 are parallel,
joining agents 0 and 2. -/
def subsidy_gadget_ends : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (0, 2)]

/-- Agent 0: edge 0 is worth 1, edges 1, 2 are worth 1/4 each, any two edges 5/4, all three 3/2.
Agent 1: edge 0 is worth 1. Agent 2: one of edges 1, 2 is worth 1/2, both 3/2. -/
noncomputable def subsidy_gadget_val : Fin 3 → Finset (Fin 3) → ℝ
  | 0, S => if 0 ∈ S then (if 1 ∈ S ∧ 2 ∈ S then 3 / 2 else if 1 ∈ S ∨ 2 ∈ S then 5 / 4 else 1)
            else (if 1 ∈ S ∧ 2 ∈ S then 5 / 4 else if 1 ∈ S ∨ 2 ∈ S then 1 / 4 else 0)
  | 1, S => if 0 ∈ S then 1 else 0
  | 2, S => if 1 ∈ S ∧ 2 ∈ S then 3 / 2 else if 1 ∈ S ∨ 2 ∈ S then 1 / 2 else 0

lemma subsidy_gadget_graph : is_graph_valuation subsidy_gadget_ends subsidy_gadget_val := by
  intro i S
  have hx : ∀ x, x ∈ S.filter (fun e => (subsidy_gadget_ends e).1 = i ∨ (subsidy_gadget_ends e).2 = i)
      ↔ x ∈ S ∧ ((subsidy_gadget_ends x).1 = i ∨ (subsidy_gadget_ends x).2 = i) :=
    fun x => Finset.mem_filter
  fin_cases i <;> simp only [subsidy_gadget_val] <;> simp only [hx] <;>
    simp (config := { decide := true }) [subsidy_gadget_ends]

lemma subsidy_gadget_monotone (i : Fin 3) : is_monotone_valuation (subsidy_gadget_val i) := by
  refine ⟨by fin_cases i <;> simp [subsidy_gadget_val], fun S T hST => ?_⟩
  have h0 := @hST 0; have h1 := @hST 1; have h2 := @hST 2
  fin_cases i <;> simp only [subsidy_gadget_val] <;>
    by_cases a0 : (0 : Fin 3) ∈ S <;> by_cases a1 : (1 : Fin 3) ∈ S <;>
    by_cases a2 : (2 : Fin 3) ∈ S <;> by_cases b0 : (0 : Fin 3) ∈ T <;>
    by_cases b1 : (1 : Fin 3) ∈ T <;> by_cases b2 : (2 : Fin 3) ∈ T <;>
    simp_all <;> norm_num

lemma subsidy_gadget_marginal (i : Fin 3) : has_max_marginal_one (subsidy_gadget_val i) := by
  refine ⟨fun S e => ?_, ?_⟩
  · fin_cases i <;> fin_cases e <;> simp only [subsidy_gadget_val] <;>
      by_cases a0 : (0 : Fin 3) ∈ S <;> by_cases a1 : (1 : Fin 3) ∈ S <;>
      by_cases a2 : (2 : Fin 3) ∈ S <;> simp [a0, a1, a2] <;> norm_num
  · fin_cases i
    · exact ⟨∅, 0, by simp [subsidy_gadget_val]⟩
    · exact ⟨∅, 0, by simp [subsidy_gadget_val]⟩
    · exact ⟨{1}, 2, by simp [subsidy_gadget_val]; norm_num⟩

lemma subsidy_gadget_lower (σ : Fin 3 → Fin 3) (p : Fin 3 → ℝ)
    (hσ : is_orientation subsidy_gadget_ends σ)
    (hef : is_envy_free_with_subsidy subsidy_gadget_val σ p) : 3 / 2 ≤ ∑ i, p i := by
  obtain ⟨hp, h⟩ := hef
  have e0 := hσ 0; have e1 := hσ 1; have e2 := hσ 2
  simp only [subsidy_gadget_ends, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
  have mem : ∀ x j, x ∈ bundle_of σ j ↔ σ x = j := by
    intro x j; simp [bundle_of]
  have h01 := h 0 1; have h02 := h 0 2; have h10 := h 1 0
  have h12 := h 1 2; have h20 := h 2 0; have h21 := h 2 1
  simp only [subsidy_gadget_val, mem] at h01 h02 h10 h12 h20 h21
  have p0 := hp 0; have p1 := hp 1; have p2 := hp 2
  simp only [Fin.sum_univ_three]
  rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;>
    simp only [e0, e1, e2] at h01 h02 h10 h12 h20 h21 <;>
    simp (config := { decide := true }) only [ite_true, ite_false,
      or_false, false_or, true_and, and_true, true_or, or_true]
      at h01 h02 h10 h12 h20 h21 <;>
    norm_num at h01 h02 h10 h12 h20 h21 <;>
    linarith

lemma subsidy_gadget_attained :
    is_orientation subsidy_gadget_ends ![1, 0, 2] ∧
      is_envy_free_with_subsidy subsidy_gadget_val ![1, 0, 2] ![3 / 4, 0, 3 / 4] := by
  refine ⟨fun e => ?_, fun i => ?_, fun i j => ?_⟩
  · fin_cases e <;> decide
  · fin_cases i <;> simp <;> norm_num
  · have mem : ∀ x j, x ∈ bundle_of (![1, 0, 2] : Fin 3 → Fin 3) j ↔ (![1, 0, 2] : Fin 3 → Fin 3) x = j := by
      intro x j; simp [bundle_of]
    fin_cases i <;> fin_cases j <;> simp [subsidy_gadget_val, mem] <;> norm_num

theorem multigraph_orientation_subsidy_three_halves :
    ∃ (ends : Fin 3 → Fin 3 × Fin 3) (v : Fin 3 → Finset (Fin 3) → ℝ),
      (∀ e, (ends e).1 ≠ (ends e).2) ∧ is_graph_valuation ends v ∧
      (∀ i, is_monotone_valuation (v i) ∧ has_max_marginal_one (v i)) ∧
      (∀ σ p, is_orientation ends σ → is_envy_free_with_subsidy v σ p → 3 / 2 ≤ ∑ i, p i) ∧
      ∃ σ p, is_orientation ends σ ∧ is_envy_free_with_subsidy v σ p ∧ ∑ i, p i = 3 / 2 := by
  refine ⟨subsidy_gadget_ends, subsidy_gadget_val, fun e => ?_, subsidy_gadget_graph,
    fun i => ⟨subsidy_gadget_monotone i, subsidy_gadget_marginal i⟩, subsidy_gadget_lower,
    ![1, 0, 2], ![3 / 4, 0, 3 / 4], subsidy_gadget_attained.1, subsidy_gadget_attained.2, ?_⟩
  · fin_cases e <;> decide
  · simp [Fin.sum_univ_three]; norm_num
