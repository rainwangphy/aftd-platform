import AFTD.Prelude

/-!
# not_card_fiber_one_eq_one

Topic: graphs   Node: 497e9208bf28

Provenance: original. Related work: refutes `card_fiber_one_eq_one`

The statement `card_fiber_one_eq_one` is false: The statement is false. The hypotheses require |A| = |P| + 1, f(A) ⊆ {c0} ∪ P, and that every c ∈ P has at least one preimage in A. However, there is no hypothesis requiring c0 to have any preimage in A.

Counterexample:
Take A = {0, 1, 2}, P = {0, 1}, c0 = 2 ∉ P.
Then |A| = 3 = |P| + 1.
Define f : A → P by f(0) = 0, f(1) = 0, f(2) = 1.
Then:
- For every x ∈ A, f(x) ∈ P ⊆ {c0} ∪ P.
- For each c ∈ P, |A ∩ f⁻¹(c)| ≥ 1 (fiber of 0 has cardinality 2, fiber of 1 has cardinality 1).
Yet A ∩ f⁻¹(c0) = ∅, so (A.filter (fun x => f x = c0)).card = 0 ≠ 1.
-/

theorem not_card_fiber_one_eq_one : ¬ (∀ {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (P : Finset β) (c0 : β) (hc0 : c0 ∉ P)
    (hA : A.card = P.card + 1)
    (f : α → β) (hf : ∀ x ∈ A, f x = c0 ∨ f x ∈ P)
    (hP : ∀ c ∈ P, 1 ≤ (A.filter (fun x => f x = c)).card), (A.filter (fun x => f x = c0)).card = 1) := by
  intro h
  let α := ULift.{u_1} (Fin 3)
  let β := ULift.{u_2} (Fin 3)
  let A : Finset α := Finset.univ
  let P : Finset β := {⟨0⟩, ⟨1⟩}
  let c0 : β := ⟨2⟩
  have hc0 : c0 ∉ P := by decide
  have hA : A.card = P.card + 1 := by decide
  let f : α → β := fun x => if x.down = 2 then ⟨1⟩ else ⟨0⟩
  have hf : ∀ x ∈ A, f x = c0 ∨ f x ∈ P := by
    intro x _
    right
    dsimp [f, P]
    split_ifs <;> decide
  have hP : ∀ c ∈ P, 1 ≤ (A.filter (fun x => f x = c)).card := by
    intro c hc
    fin_cases hc
    · have h0 : (⟨0⟩ : α) ∈ A.filter (fun x => f x = ⟨0⟩) := by
        simp [A, f]
      exact Finset.card_pos.mpr ⟨_, h0⟩
    · have h1 : (⟨2⟩ : α) ∈ A.filter (fun x => f x = ⟨1⟩) := by
        simp [A, f]
      exact Finset.card_pos.mpr ⟨_, h1⟩
  have h_res := @h α β _ _ A P c0 hc0 hA f hf hP
  have h_empty : A.filter (fun x => f x = c0) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro ⟨x⟩ _
    dsimp [f, c0]
    revert x
    decide
  rw [h_empty, Finset.card_empty] at h_res
  revert h_res
  decide
