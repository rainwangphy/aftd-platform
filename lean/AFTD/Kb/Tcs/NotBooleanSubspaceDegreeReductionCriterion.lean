import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanTopForm
import AFTD.Kb.Tcs.BooleanDegree
import AFTD.Kb.Tcs.BooleanAffineRestriction

/-!
# not_boolean_subspace_degree_reduction_criterion

Topic: combinatorics   Node: 57b6f4ea6b40

Provenance: original. Related work: refutes `boolean_subspace_degree_reduction_criterion`

The statement `boolean_subspace_degree_reduction_criterion` is false: The statement is false for d = 0.
When d = 0:
Let n = 1, p : (Fin 1 → ZMod 2) → ZMod 2 be the constant 1 function, and U = ⊥.
1. booleanDegree p = 0, because the ANF coefficient for S = ∅ is p(0) = 1 ≠ 0, while for S = {0} the sum is p(0) + p(1) = 2 = 0 in ZMod 2. Thus hp : booleanDegree p = 0 holds.
2. For U = ⊥, Module.finrank (ZMod 2) ↥⊥ = 0. Any function on Fin 0 → ZMod 2 has booleanDegree ≤ 0. In Lean's natural number arithmetic, d - 1 = 0 - 1 = 0. Thus booleanDegree (booleanAffineRestriction p a ⊥) ≤ 0 - 1 holds for all a, so the RHS of the equivalence is TRUE.
3. The LHS states that booleanTopForm 0 p u = 0 for all u : Fin 0 → (Fin 1 → ZMod 2). But by definition, booleanTopForm 0 p u = ∑ S : Finset (Fin 0), p (∑ i ∈ S, u i) = p(0) = 1 ≠ 0. Thus the LHS is FALSE.
Since LHS is false and RHS is true, the equivalence fails.
-/

theorem not_boolean_subspace_degree_reduction_criterion : ¬ (∀ {n d : ℕ}
    (p : (Fin n → ZMod 2) → ZMod 2) (hp : booleanDegree p = d)
    (U : Submodule (ZMod 2) (Fin n → ZMod 2)), (∀ u : Fin d → (Fin n → ZMod 2), (∀ i, u i ∈ U) → booleanTopForm d p u = 0) ↔
      (∀ a : Fin n → ZMod 2, booleanDegree (booleanAffineRestriction p a U) ≤ d - 1)) := by
  intro h
  have test_deg : booleanDegree (fun (_ : Fin 1 → ZMod 2) => (1 : ZMod 2)) = 0 := by
    dsimp [booleanDegree]
    apply le_antisymm
    · apply Finset.sup_le
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      by_contra hc
      have hS_card : S.card = 1 := by
        have := Finset.card_le_univ S
        simp only [Fintype.card_fin] at this
        omega
      have hS_univ : S = Finset.univ := by
        rw [← Finset.card_eq_iff_eq_univ]
        rw [Fintype.card_fin]
        exact hS_card
      subst hS_univ
      have h_sum : (∑ x ∈ Finset.univ.filter (fun (x : Fin 1 → ZMod 2) => ∀ i, x i ≠ 0 → i ∈ (Finset.univ : Finset (Fin 1))), (1 : ZMod 2)) = 0 := by
        have : (Finset.univ.filter (fun (x : Fin 1 → ZMod 2) => ∀ i, x i ≠ 0 → i ∈ (Finset.univ : Finset (Fin 1)))) = Finset.univ := by
          ext x; simp
        rw [this]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          ZMod.card, nsmul_eq_mul, mul_one]
        rfl
      exact hS h_sum
    · exact Nat.zero_le _
  have q_deg : ∀ (k : ℕ) (f : (Fin k → ZMod 2) → ZMod 2), booleanDegree f ≤ k := by
    intro k f
    dsimp [booleanDegree]
    apply Finset.sup_le
    intro S _
    have := Finset.card_le_univ S
    simp only [Fintype.card_fin] at this
    exact this
  have h_spec := @h 1 0 (fun _ => 1) test_deg ⊥
  have h_rhs : ∀ a : Fin 1 → ZMod 2, booleanDegree (booleanAffineRestriction (fun _ => 1) a ⊥) ≤ 0 - 1 := by
    intro a
    have h_deg := q_deg (Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) (Fin 1 → ZMod 2))) (booleanAffineRestriction (fun _ => 1) a ⊥)
    have h_rk : Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) (Fin 1 → ZMod 2)) = 0 :=
      finrank_bot (ZMod 2) (Fin 1 → ZMod 2)
    omega
  have h_lhs := h_spec.mpr h_rhs
  have h_u_in : ∀ i : Fin 0, (fun _ : Fin 0 => (0 : Fin 1 → ZMod 2)) i ∈ (⊥ : Submodule (ZMod 2) (Fin 1 → ZMod 2)) := by
    intro i
    exact Fin.elim0 i
  have h_zero := h_lhs (fun _ => 0) h_u_in
  dsimp [booleanTopForm] at h_zero
  have h_univ : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by
    decide
  rw [h_univ] at h_zero
  simp only [Finset.sum_singleton] at h_zero
  revert h_zero
  decide
