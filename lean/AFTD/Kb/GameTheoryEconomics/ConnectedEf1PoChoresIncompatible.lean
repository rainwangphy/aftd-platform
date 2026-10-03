import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsConnectedAllocation
import AFTD.Kb.GameTheoryEconomics.IsEf1Chores
import AFTD.Kb.GameTheoryEconomics.IsConnectedPoChores
import AFTD.Kb.GameTheoryEconomics.IsPathConnected
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# connected_ef1_po_chores_incompatible

Topic: fair_division   Node: e24dcb0089ca

For chores on a path with additive, strictly positive costs, EF1 and Pareto optimality (among connected allocations) can be incompatible: with three agents and five chores, costs (4,2,1,2,2) for agent 0 and (1,4,1,2,2) for agents 1 and 2, each of the 12 connected EF1 allocations is Pareto-dominated by a connected allocation with cost vector (5,1,2), (2,1,5) or (2,5,1). Since EF1outer implies EF1, EF1outer and PO are incompatible as well.
-/

/-- Costs of the counterexample: agent 0 pays (4, 2, 1, 2, 2), agents 1 and 2 pay (1, 4, 1, 2, 2). -/
def chores_path_cost : Fin 3 → Fin 5 → ℕ :=
  ![![4, 2, 1, 2, 2], ![1, 4, 1, 2, 2], ![1, 4, 1, 2, 2]]

/-- Agent `i`'s cost for agent `k`'s bundle under `σ`, in `ℕ`. -/
abbrev chores_path_bc (σ : Fin 5 → Fin 3) (i k : Fin 3) : ℕ :=
  ∑ e ∈ bundle_of σ k, chores_path_cost i e

/-- `τ` Pareto-dominates `σ` for the costs `chores_path_cost`. -/
abbrev chores_path_dom (τ σ : Fin 5 → Fin 3) : Prop :=
  (∀ i, chores_path_bc τ i i ≤ chores_path_bc σ i i) ∧ ∃ i, chores_path_bc τ i i < chores_path_bc σ i i

/-- Connectedness of an allocation of the five chores, spelled out over `Fin 5`. -/
lemma chores_path_conn_iff (σ : Fin 5 → Fin 3) : is_connected_allocation σ ↔
    ∀ i : Fin 3, ∀ x ∈ bundle_of σ i, ∀ y ∈ bundle_of σ i, ∀ z : Fin 5,
      x ≤ z → z ≤ y → z ∈ bundle_of σ i := Iff.rfl

/-- The property checked for each allocation `σ` of the five chores: if `σ` is connected and
EF1, one of three connected allocations, with cost vectors (5, 1, 2), (2, 1, 5) and (2, 5, 1),
Pareto-dominates it. -/
def chores_path_ok (σ : Fin 5 → Fin 3) : Prop :=
  (∀ i : Fin 3, ∀ x ∈ bundle_of σ i, ∀ y ∈ bundle_of σ i, ∀ z : Fin 5,
      x ≤ z → z ≤ y → z ∈ bundle_of σ i) →
    (∀ i j, chores_path_bc σ i i ≤ chores_path_bc σ i j ∨
      ∃ x ∈ bundle_of σ i, chores_path_bc σ i i ≤ chores_path_cost i x + chores_path_bc σ i j) →
    chores_path_dom ![1, 0, 0, 0, 2] σ ∨ chores_path_dom ![1, 0, 2, 2, 2] σ ∨
      chores_path_dom ![2, 0, 1, 1, 1] σ

instance chores_path_ok_decidable : DecidablePred chores_path_ok := fun σ => by
  unfold chores_path_ok; infer_instance

/-- The kernel check, over all 243 allocations. -/
lemma chores_path_check : ∀ a b c d e : Fin 3, chores_path_ok ![a, b, c, d, e] := by
  decide

theorem connected_ef1_po_chores_incompatible :
    ∃ c : Fin 3 → Fin 5 → ℝ, (∀ i e, 0 < c i e) ∧
      ¬ ∃ σ : Fin 5 → Fin 3,
        is_connected_allocation σ ∧ is_ef1_chores c σ ∧ is_connected_po_chores c σ := by
  refine ⟨fun i e => (chores_path_cost i e : ℝ), fun i e => ?_, ?_⟩
  · have : 0 < chores_path_cost i e := by revert i e; decide
    show (0 : ℝ) < (chores_path_cost i e : ℝ)
    exact_mod_cast this
  rintro ⟨σ, hconn, hef1, hpo⟩
  have hav : ∀ τ : Fin 5 → Fin 3, ∀ i k, additive_valuation (fun e => (chores_path_cost i e : ℝ))
      (bundle_of τ k) = (chores_path_bc τ i k : ℝ) := by
    intro τ i k; simp [additive_valuation, chores_path_bc]
  have hσ : σ = ![σ 0, σ 1, σ 2, σ 3, σ 4] := by
    funext x; fin_cases x <;> rfl
  have hef : ∀ i j, chores_path_bc σ i i ≤ chores_path_bc σ i j ∨
      ∃ x ∈ bundle_of σ i, chores_path_bc σ i i ≤ chores_path_cost i x + chores_path_bc σ i j := by
    intro i j
    rcases hef1 i j with h | ⟨x, hx, h⟩
    · left; rw [hav, hav] at h; exact_mod_cast h
    · right; refine ⟨x, hx, ?_⟩
      rw [hav, hav] at h
      have : (chores_path_bc σ i i : ℝ) ≤ (chores_path_cost i x : ℝ) + chores_path_bc σ i j := by
        linarith
      exact_mod_cast this
  rw [hσ] at hconn hef
  have hdom := chores_path_check _ _ _ _ _ ((chores_path_conn_iff _).1 hconn) hef
  rw [← hσ] at hdom
  apply hpo
  have lift : ∀ τ, is_connected_allocation τ → chores_path_dom τ σ →
      ∃ τ, is_connected_allocation τ ∧
        (∀ i, additive_valuation (fun e => (chores_path_cost i e : ℝ)) (bundle_of τ i) ≤
          additive_valuation (fun e => (chores_path_cost i e : ℝ)) (bundle_of σ i)) ∧
        ∃ i, additive_valuation (fun e => (chores_path_cost i e : ℝ)) (bundle_of τ i) <
          additive_valuation (fun e => (chores_path_cost i e : ℝ)) (bundle_of σ i) := by
    rintro τ hτ ⟨hle, i, hlt⟩
    refine ⟨τ, hτ, fun k => ?_, i, ?_⟩
    · rw [hav, hav]; exact_mod_cast hle k
    · rw [hav, hav]; exact_mod_cast hlt
  rcases hdom with h | h | h
  · exact lift _ ((chores_path_conn_iff _).2 (by decide)) h
  · exact lift _ ((chores_path_conn_iff _).2 (by decide)) h
  · exact lift _ ((chores_path_conn_iff _).2 (by decide)) h
