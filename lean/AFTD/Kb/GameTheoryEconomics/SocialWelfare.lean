import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# social_welfare

Topic: fair_division   Node: d636ff6d4309

Provenance: formalization of a published result. Source: arXiv:2611.12740 Section 7

The utilitarian social welfare of an allocation X under a homogeneous additive valuation v is the sum of values v(X_i) over all agents i.
-/

/-- Utilitarian social welfare of an allocation under a homogeneous valuation. -/
def social_welfare {m n : ℕ} (v : Fin m → ℝ) (X : Fin n → Finset (Fin m)) : ℝ := ∑ i, additive_valuation v (X i)
