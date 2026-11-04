import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAlphaMmsChores

/-!
# is_ex_post_alpha_mms_chores

Topic: fair_division   Node: e3f28ba95e6c

Provenance: formalization of a published result. Source: arXiv:2611.04884, Section 2

An allocation lottery p over allocations of m chores among n agents is ex-post α-MMS for chore costs c if every allocation σ in the support of p (having p σ > 0) is α-MMS for c.
-/

/-- An allocation lottery is ex-post α-MMS for chores if every allocation in its support is α-MMS. -/
def is_ex_post_alpha_mms_chores {m n : ℕ} (α : ℝ) (c : Fin n → Fin m → ℝ)
    (p : (Fin m → Fin n) → ℝ) : Prop :=
  ∀ σ : Fin m → Fin n, 0 < p σ → is_alpha_mms_chores α c σ
