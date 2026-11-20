import AFTD.Prelude
import AFTD.Kb.Tcs.ThrCond
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.CnfLitCompl
import AFTD.Kb.Tcs.CnfLitDecidableEq

/-!
# is_thr_res_derivation

Topic: proof_complexity   Node: 70bbf5495e91

Provenance: formalization of a published result. Source: arXiv:2611.24548 Definition 2.12

A Threshold Resolution (Thr-Res) derivation from a CNF formula F : Finset (Finset (CnfLit (Fin n))) is a list π : List (ThrCond n) where each line π[i] satisfies at least one of six rules: (1) Source: for all l, π[i].coeffs l = 0 and π[i].threshold = 0; (2) Clause introduction: there exist j < i and C ∈ F such that for all l, π[i].coeffs l = π[j].coeffs l + (if l ∈ C then 1 else 0) and π[i].threshold = π[j].threshold + 1; (3) Resolution: there exist j < i, k < i, and variable v : Fin n such that for all l, π[j].coeffs l = π[i].coeffs l + (if l = CnfLit.pos v then 1 else 0), and π[k].coeffs l = π[i].coeffs l + (if l = CnfLit.neg v then 1 else 0), and π[j].threshold = π[i].threshold and π[k].threshold = π[i].threshold; (4) Weakening: there exist j < i and literal l₀ such that for all l, π[i].coeffs l = π[j].coeffs l + (if l = l₀ then 1 else 0) and π[i].threshold = π[j].threshold; (5) Introduce: there exist j < i and literal l₀ such that for all l, π[i].coeffs l = π[j].coeffs l + (if l = l₀ ∨ l = cnf_lit_compl l₀ then 1 else 0) and π[i].threshold = π[j].threshold + 1; or (6) Simplify: there exist j < i and literal l₀ such that for all l, π[j].coeffs l = π[i].coeffs l + (if l = l₀ ∨ l = cnf_lit_compl l₀ then 1 else 0) and π[j].threshold = π[i].threshold + 1.
-/

/-- A Threshold Resolution (Thr-Res) derivation from a CNF formula F. -/
def is_thr_res_derivation (n : ℕ) (F : Finset (Finset (CnfLit (Fin n)))) (π : List (ThrCond n)) : Prop :=
  ∀ i : Fin π.length,
    ( (∀ l, π[i].coeffs l = 0) ∧ π[i].threshold = 0 ) ∨
    ( ∃ (j : Fin π.length) (C : Finset (CnfLit (Fin n))),
        j < i ∧ C ∈ F ∧
        (∀ l, π[i].coeffs l = π[j].coeffs l + if l ∈ C then 1 else 0) ∧
        π[i].threshold = π[j].threshold + 1 ) ∨
    ( ∃ (j k : Fin π.length) (v : Fin n),
        j < i ∧ k < i ∧
        (∀ l, π[j].coeffs l = π[i].coeffs l + if l = CnfLit.pos v then 1 else 0) ∧
        (∀ l, π[k].coeffs l = π[i].coeffs l + if l = CnfLit.neg v then 1 else 0) ∧
        π[j].threshold = π[i].threshold ∧ π[k].threshold = π[i].threshold ) ∨
    ( ∃ (j : Fin π.length) (l₀ : CnfLit (Fin n)),
        j < i ∧
        (∀ l, π[i].coeffs l = π[j].coeffs l + if l = l₀ then 1 else 0) ∧
        π[i].threshold = π[j].threshold ) ∨
    ( ∃ (j : Fin π.length) (l₀ : CnfLit (Fin n)),
        j < i ∧
        (∀ l, π[i].coeffs l = π[j].coeffs l + (if l = l₀ ∨ l = cnf_lit_compl l₀ then 1 else 0)) ∧
        π[i].threshold = π[j].threshold + 1 ) ∨
    ( ∃ (j : Fin π.length) (l₀ : CnfLit (Fin n)),
        j < i ∧
        (∀ l, π[j].coeffs l = π[i].coeffs l + (if l = l₀ ∨ l = cnf_lit_compl l₀ then 1 else 0)) ∧
        π[j].threshold = π[i].threshold + 1 )
