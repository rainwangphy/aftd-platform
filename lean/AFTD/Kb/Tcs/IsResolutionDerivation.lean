import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# is_resolution_derivation

Topic: proof_complexity   Node: 65c39a4f6239

A resolution derivation from a CNF formula F (a finite set of clauses, each a finite set of literals) is a sequence of clauses C_1, ..., C_s in which each C_i is in F, or is a weakening C_i = C_j or E (C_j a subset of C_i) of an earlier clause, or is the resolvent C or D of earlier clauses C_j = C or x and C_k = D or not x.
-/

/-- A resolution derivation from F: a sequence of clauses each of which is in F, or a weakening of an earlier clause, or the resolvent of two earlier clauses. -/
def is_resolution_derivation {V : Type*} (F : Finset (Finset (CnfLit V))) (π : List (Finset (CnfLit V))) : Prop :=
  ∀ i : Fin π.length,
    π[i] ∈ F ∨
    (∃ j : Fin π.length, j < i ∧ π[j] ⊆ π[i]) ∨
    (∃ j k : Fin π.length, j < i ∧ k < i ∧ ∃ (x : V) (C D : Finset (CnfLit V)),
      (∀ l, l ∈ π[j] ↔ l ∈ C ∨ l = CnfLit.pos x) ∧ (∀ l, l ∈ π[k] ↔ l ∈ D ∨ l = CnfLit.neg x) ∧
      (∀ l, l ∈ π[i] ↔ l ∈ C ∨ l ∈ D))
