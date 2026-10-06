import AFTD.Prelude

/-!
# tfjr_avoid

Topic: social_choice   Node: d86c6ffb712d

Provenance: helper lemma. step towards temporal_droop_fjr_not_imp_bfjr (Droop-FJR vs BFJR, arXiv:2505.22513, App. A.3)

Any two rounds out of six miss some round among 0-2 and some round among 3-5 (checked by decide).
-/

/-- Any two rounds out of six miss some round among 0-2 and some round among 3-5 (checked by decide). -/
theorem tfjr_avoid : ∀ D : Finset (Fin 6), D.card ≤ 2 →
    ∃ r₁ r₂ : Fin 6, r₁.val < 3 ∧ 3 ≤ r₂.val ∧ r₁ ∉ D ∧ r₂ ∉ D := by
  decide
