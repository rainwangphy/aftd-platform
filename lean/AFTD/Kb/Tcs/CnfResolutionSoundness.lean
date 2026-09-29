import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_resolution_soundness

Topic: np_completeness   Node: 1765413b1f1b

Soundness of the resolution rule: for any truth assignment `τ : V → Bool`, variable `v : V`, and clauses `C, D : List (CnfLit V)`, if there exists a literal in `C ++ [CnfLit.pos v]` satisfied by `τ` (that is, `match l with | CnfLit.pos u => τ u = true | CnfLit.neg u => τ u = false`) and a literal in `D ++ [CnfLit.neg v]` satisfied by `τ`, then there exists a literal in `C ++ D` satisfied by `τ`.
-/

/-- Soundness of the resolution rule: if an assignment satisfies both C ∨ v and D ∨ ¬v, it satisfies C ∨ D. -/
theorem cnf_resolution_soundness {V : Type*} (τ : V → Bool) (v : V)
    (C D : List (CnfLit V))
    (hC : ∃ l ∈ C ++ [CnfLit.pos v], match l with | CnfLit.pos u => τ u = true | CnfLit.neg u => τ u = false)
    (hD : ∃ l ∈ D ++ [CnfLit.neg v], match l with | CnfLit.pos u => τ u = true | CnfLit.neg u => τ u = false) :
    ∃ l ∈ C ++ D, match l with | CnfLit.pos u => τ u = true | CnfLit.neg u => τ u = false := by
  cases hv : τ v
  · rcases hC with ⟨l, hl, hsat⟩
    rw [List.mem_append] at hl
    cases hl with
    | inl hlC =>
      refine ⟨l, List.mem_append_left D hlC, hsat⟩
    | inr hlv =>
      simp only [List.mem_singleton] at hlv
      subst hlv
      dsimp at hsat
      rw [hv] at hsat
      contradiction
  · rcases hD with ⟨l, hl, hsat⟩
    rw [List.mem_append] at hl
    cases hl with
    | inl hlD =>
      refine ⟨l, List.mem_append_right C hlD, hsat⟩
    | inr hlv =>
      simp only [List.mem_singleton] at hlv
      subst hlv
      dsimp at hsat
      rw [hv] at hsat
      contradiction
