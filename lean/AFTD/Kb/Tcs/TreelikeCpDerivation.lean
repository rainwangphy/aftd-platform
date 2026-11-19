import AFTD.Prelude
import AFTD.Kb.Tcs.LinIneq
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.CnfClauseToLin
import AFTD.Kb.Tcs.CnfLitDecidableEq

/-!
# TreelikeCpDerivation

Topic: proof_complexity   Node: 54f92452fd1c

Provenance: formalization of a published result. Source: arXiv:2611.24548 Def 4.1

Inductive type family of treelike Cutting Planes (CP) derivations of a linear inequality from a CNF formula F over n variables (given as a List of clauses, each a List of CnfLit (Fin n)): constructors are the trivial line 0 ≥ 0, box lower bounds x_i ≥ 0, box upper bounds -x_i ≥ -1, clause embeddings cnf_clause_to_lin n C.toFinset for C ∈ F, nonnegative integer linear combination of two sub-derivations with multipliers lam1 lam2 : ℕ, and integer division (rounding) of a sub-derivation by α : ℕ (α > 0) when α divides all coefficients.
-/

/-- Inductive family of treelike Cutting Planes derivations from a CNF formula F. -/
inductive TreelikeCpDerivation (n : ℕ) (F : List (List (CnfLit (Fin n)))) : LinIneq n → Type | trivial : TreelikeCpDerivation n F { coeffs := fun _ => 0, const := 0 }
  | box_lower (i : Fin n) :
      TreelikeCpDerivation n F { coeffs := fun j => if j = i then 1 else 0, const := 0 }
  | box_upper (i : Fin n) :
      TreelikeCpDerivation n F { coeffs := fun j => if j = i then -1 else 0, const := -1 }
  | clause (C : List (CnfLit (Fin n))) (hC : C ∈ F) :
      TreelikeCpDerivation n F (cnf_clause_to_lin n C.toFinset)
  | lin_comb {L₁ L₂ : LinIneq n}
      (d₁ : TreelikeCpDerivation n F L₁) (d₂ : TreelikeCpDerivation n F L₂) (lam1 lam2 : ℕ) :
      TreelikeCpDerivation n F
        { coeffs := fun j => (lam1 : ℤ) * L₁.coeffs j + (lam2 : ℤ) * L₂.coeffs j,
          const := (lam1 : ℤ) * L₁.const + (lam2 : ℤ) * L₂.const }
  | division {L : LinIneq n} (d : TreelikeCpDerivation n F L)
      (c : Fin n → ℤ) (α : ℕ) (hα : 0 < α) (hdiv : ∀ j, L.coeffs j = (α : ℤ) * c j) :
      TreelikeCpDerivation n F { coeffs := c, const := Int.ceil ((L.const : ℚ) / α) }
