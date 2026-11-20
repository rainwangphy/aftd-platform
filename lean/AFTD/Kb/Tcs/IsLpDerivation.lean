import AFTD.Prelude
import AFTD.Kb.Tcs.LinIneq
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.CnfLitDecidableEq

/-!
# is_lp_derivation

Topic: proof_complexity   Node: 6f445f9d30b4

Provenance: formalization of a published result. Source: arXiv:2611.24548 Definition 4.2

A Lift & Project (L&P) derivation from a CNF formula F : Finset (Finset (CnfLit (Fin n))) is a list π : List (LinIneq n) where each line π[i] is: (1) the trivial line 0 ≥ 0; (2) a Boolean box axiom x_v ≥ 0 or -x_v ≥ -1 for some v : Fin n; (3) an embedded clause C ∈ F; (4) a linear combination of two earlier lines π[j], π[k] (j, k < i) with non-negative integer coefficients lam1, lam2 : ℕ; or (5) a Lift & Project cut from two earlier lines π[j], π[k] (j, k < i) with arbitrary coefficient vector c : Fin n → ℤ, variable v : Fin n, and integers d, d', d'' : ℤ, such that π[j].coeffs = c, π[j].const = d - d', π[k].coeffs = c + d'' * e_v, π[k].const = d, concluding π[i].coeffs = c + d' * e_v and π[i].const = d.
-/

/-- A Lift & Project (L&P) derivation from a CNF formula F. -/
def is_lp_derivation (n : ℕ) (F : Finset (Finset (CnfLit (Fin n)))) (π : List (LinIneq n)) : Prop :=
  ∀ i : Fin π.length,
    ( (∀ j, π[i].coeffs j = 0) ∧ π[i].const = 0 ) ∨
    ( ∃ v : Fin n, (∀ j, π[i].coeffs j = if j = v then 1 else 0) ∧ π[i].const = 0 ) ∨
    ( ∃ v : Fin n, (∀ j, π[i].coeffs j = if j = v then -1 else 0) ∧ π[i].const = -1 ) ∨
    ( ∃ C ∈ F,
        (∀ j, π[i].coeffs j = (if CnfLit.pos j ∈ C then 1 else 0) - (if CnfLit.neg j ∈ C then 1 else 0)) ∧
        π[i].const = 1 - ∑ j : Fin n, (if CnfLit.neg j ∈ C then (1 : ℤ) else 0) ) ∨
    ( ∃ (j k : Fin π.length) (lam1 lam2 : ℕ),
        j < i ∧ k < i ∧
        (∀ m, π[i].coeffs m = (lam1 : ℤ) * π[j].coeffs m + (lam2 : ℤ) * π[k].coeffs m) ∧
        π[i].const = (lam1 : ℤ) * π[j].const + (lam2 : ℤ) * π[k].const ) ∨
    ( ∃ (j k : Fin π.length) (c : Fin n → ℤ) (v : Fin n) (d d' d'' : ℤ),
        j < i ∧ k < i ∧
        (∀ m, π[j].coeffs m = c m) ∧ π[j].const = d - d' ∧
        (∀ m, π[k].coeffs m = c m + if m = v then d'' else 0) ∧ π[k].const = d ∧
        (∀ m, π[i].coeffs m = c m + if m = v then d' else 0) ∧ π[i].const = d )
