import AFTD.Prelude

/-!
# PaymentWindow

Topic: online_algorithms   Node: 39f16ac34ff8

Provenance: formalization of a published result. Source: arXiv:2610.18767 Section 3.2, Lemma 3.4

A structure PaymentWindow parameterized by page type α and cache capacity k : ℕ, consisting of a requested page : α, offline fetch count delta_fetches_opt : ℕ, offline delay cost delta_delay_opt : ℝ with 0 ≤ delta_delay_opt, an integer rank potential change delta_phi : ℤ, and a proof of case_condition stating that delta_phi ≤ -1, or (1 ≤ delta_fetches_opt and delta_phi ≤ k), or (1 ≤ delta_delay_opt and delta_phi ≤ k).
-/

/-- Payment window capturing offline actions and potential change for one online payment. -/
structure PaymentWindow (α : Type*) (k : ℕ) where
  page : α
  delta_fetches_opt : ℕ
  delta_delay_opt : ℝ
  delta_delay_nonneg : 0 ≤ delta_delay_opt
  delta_phi : ℤ
  case_condition :
    delta_phi ≤ -1 ∨
    (1 ≤ delta_fetches_opt ∧ delta_phi ≤ (k : ℤ)) ∨
    (1 ≤ delta_delay_opt ∧ delta_phi ≤ (k : ℤ))
