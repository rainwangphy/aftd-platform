import AFTD.Prelude
import AFTD.Kb.Tcs.CnfSatisfiable
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_single_clause_satisfiable_iff

Topic: np_completeness   Node: 5c06d478e75b

A CNF formula consisting of a single clause `c`, namely `[c]`, is satisfiable (`CnfSatisfiable [c]`) if and only if the clause `c` is non-empty (`c ≠ []`).
-/

/-- A single-clause CNF formula [c] is satisfiable if and only if the clause c is non-empty. -/
theorem cnf_single_clause_satisfiable_iff {V : Type*} (c : List (CnfLit V)) :
    CnfSatisfiable [c] ↔ c ≠ [] := by
  constructor
  · rintro ⟨τ, hτ⟩ rfl
    obtain ⟨l, hl, -⟩ := hτ [] (List.Mem.head _)
    cases hl
  · intro hc
    cases c with
    | nil => contradiction
    | cons l ls =>
      cases l with
      | pos v =>
        use (fun _ => true)
        intro c' hc'
        obtain rfl := List.mem_singleton.mp hc'
        exact ⟨CnfLit.pos v, List.Mem.head _, rfl⟩
      | neg v =>
        use (fun _ => false)
        intro c' hc'
        obtain rfl := List.mem_singleton.mp hc'
        exact ⟨CnfLit.neg v, List.Mem.head _, rfl⟩
