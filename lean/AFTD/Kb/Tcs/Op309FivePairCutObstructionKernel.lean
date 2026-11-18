import AFTD.Prelude

/-!
# op309_five_pair_cut_obstruction_kernel

Topic: graphs   Node: b8fd7dbe0f66

Provenance: helper lemma. Finite kernel for the prescribed perfect matching cut obstruction of OP-309, experiments 31275 and 31278.

For every assignment of five Boolean values, at least one of the fifteen displayed equality patterns holds.
-/

theorem op309_five_pair_cut_obstruction_kernel :
    ∀ a0 a1 a2 a3 a4 : Bool,
      (a0 = a1 ∧ a0 = a2 ∧ a0 = a3 ∧ a0 = a4) ∨
      (a0 = a3 ∧ a3 = a4) ∨
      (a0 = a4 ∧ a1 = a3) ∨
      (a0 = a2 ∧ a1 = a3) ∨
      (a0 = a1 ∧ a0 = a3) ∨
      (a0 = a1 ∧ a1 = a2 ∧ a1 = a3 ∧ a1 = a4) ∨
      (a0 = a1 ∧ a1 = a2) ∨
      (a0 = a2 ∧ a1 = a4) ∨
      (a0 = a2 ∧ a1 = a2 ∧ a2 = a3 ∧ a2 = a4) ∨
      (a0 = a4 ∧ a2 = a3) ∨
      (a0 = a3 ∧ a1 = a3 ∧ a2 = a3 ∧ a3 = a4) ∨
      (a2 = a4 ∧ a3 = a4) ∨
      (a0 = a4 ∧ a1 = a4 ∧ a2 = a4 ∧ a3 = a4) ∨
      (a1 = a2 ∧ a2 = a4) ∨
      (a1 = a4 ∧ a2 = a3) := by
  intro a0 a1 a2 a3 a4
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> decide
