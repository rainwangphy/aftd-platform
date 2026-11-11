import AFTD.Prelude
import AFTD.Kb.Tcs.IntervalPoset
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# is_m_interval_poset

Topic: combinatorics   Node: 13eec0d6fdf1

Provenance: formalization of a published result. Source: arXiv:1311.3922 Def. 4.5

An m-interval-poset of size n is an interval-poset on Fin (n * m) where within each block of size m, the elements are ordered in decreasing order: (i * m + j₂) ≺ (i * m + j₁) for j₁ < j₂.
-/

/-- Predicate for a synchronized m-interval-poset of size n, whose blocks of size m are decreasingly ordered. -/
def is_m_interval_poset (m n : ℕ) (P : IntervalPoset (Fin (n * m))) : Prop := ∀ (i : ℕ) (hi : i < n) (j₁ j₂ : ℕ) (hj₁ : j₁ < m) (hj₂ : j₂ < m),
    j₁ < j₂ →
      P.rel ⟨i * m + j₂, by nlinarith⟩ ⟨i * m + j₁, by nlinarith⟩
