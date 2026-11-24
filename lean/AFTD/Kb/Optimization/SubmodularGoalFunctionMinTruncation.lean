import AFTD.Prelude
import AFTD.Kb.Optimization.IsSubmodularGoalFunction
import AFTD.Kb.Optimization.IsMstCertificate
import AFTD.Kb.Optimization.PartialAssignmentLe

/-!
# submodular_goal_function_min_truncation

Topic: submodular   Node: 02a6c93fa950

Provenance: helper lemma. step towards op_853_polynomial_submodular_goal_value_bound

If φ is a monotone submodular potential on partial assignments with φ(empty assignment) = 0 and φ(β) ≥ Q exactly on the MST identification certificates, then its truncation min(φ, Q) is a submodular goal function with goal value Q.
-/

lemma submodular_goal_function_min_truncation_none {E : Type*} {β γ : E → Option Bool}
    (hle : partial_assignment_le β γ) {e : E} (he : γ e = none) : β e = none := by
  cases h : β e with
  | none => rfl
  | some b =>
    have := hle e b h
    rw [he] at this
    cases this

lemma submodular_goal_function_min_truncation_self_update {E : Type*} [DecidableEq E]
    (β : E → Option Bool) (e : E) (s : Bool)
    (he : β e = none) : partial_assignment_le β (Function.update β e (some s)) := by
  intro e' b hb
  by_cases h : e' = e
  · subst h
    rw [he] at hb
    cases hb
  · rw [Function.update_of_ne h]
    exact hb

lemma submodular_goal_function_min_truncation_update_update {E : Type*} [DecidableEq E]
    {β γ : E → Option Bool}
    (hle : partial_assignment_le β γ) (e : E) (s : Bool) :
    partial_assignment_le (Function.update β e (some s)) (Function.update γ e (some s)) := by
  intro e' b hb
  by_cases h : e' = e
  · subst h
    rw [Function.update_self] at hb ⊢
    exact hb
  · rw [Function.update_of_ne h] at hb ⊢
    exact hle e' b hb

open scoped Classical in
/-- Truncating a certificate-separating monotone submodular potential at Q yields a genuine submodular goal function. -/
theorem submodular_goal_function_min_truncation {V : Type*} [Fintype V]
    (G : SimpleGraph V) (φ : (G.edgeSet → Option Bool) → ℕ) (Q : ℕ)
    (h0 : φ (fun _ => none) = 0)
    (hmono : ∀ β γ, partial_assignment_le β γ → φ β ≤ φ γ)
    (hsub : ∀ β γ e s, partial_assignment_le β γ → γ e = none →
      φ (Function.update γ e (some s)) + φ β ≤ φ (Function.update β e (some s)) + φ γ)
    (hcert : ∀ β, Q ≤ φ β ↔ is_mst_certificate G β) :
    is_submodular_goal_function G (fun β => min (φ β) Q) Q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1: empty assignment
    dsimp
    rw [h0]
    exact min_eq_left (Nat.zero_le Q)
  · -- 2: monotonicity
    intro β γ hle
    dsimp
    exact min_le_min (hmono β γ hle) le_rfl
  · -- 3: submodularity
    intro β γ e s hle hγe
    dsimp
    have hβe : β e = none := submodular_goal_function_min_truncation_none hle hγe
    have h_ba : φ (Function.update β e (some s)) ≤ φ (Function.update γ e (some s)) :=
      hmono _ _ (submodular_goal_function_min_truncation_update_update hle e s)
    have h_cd : φ β ≤ φ γ := hmono _ _ hle
    have h_cb : φ β ≤ φ (Function.update β e (some s)) :=
      hmono _ _ (submodular_goal_function_min_truncation_self_update β e s hβe)
    have h_da : φ γ ≤ φ (Function.update γ e (some s)) :=
      hmono _ _ (submodular_goal_function_min_truncation_self_update γ e s hγe)
    have h_sub : φ (Function.update γ e (some s)) + φ β ≤ φ (Function.update β e (some s)) + φ γ :=
      hsub β γ e s hle hγe
    simp only [Nat.min_def]
    split <;> split <;> split <;> split <;> omega
  · -- 4: certificate condition
    intro β
    dsimp
    rw [min_eq_right_iff]
    exact hcert β
