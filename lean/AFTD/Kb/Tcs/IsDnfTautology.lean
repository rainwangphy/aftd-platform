import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# is_dnf_tautology

Topic: proof_complexity   Node: 0395be8c9f63

Provenance: formalization of a published result. Source: arXiv:2611.01055, Section 2.2

A DNF formula A is a tautology if for every Boolean truth assignment to its variables, at least one conjunction term in A is satisfied.
-/

/-- A DNF formula is a tautology if every truth assignment satisfies at least one term. -/
def is_dnf_tautology {V : Type*} (A : List (List (CnfLit V))) : Prop := ∀ τ : V → Bool, ∃ t ∈ A, ∀ l ∈ t, match l with
    | CnfLit.pos v => τ v = true
    | CnfLit.neg v => τ v = false
