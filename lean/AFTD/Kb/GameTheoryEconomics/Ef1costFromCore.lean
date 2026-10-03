import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Ef1costEf1OfPair
import AFTD.Kb.GameTheoryEconomics.Ef1costPairOk
import AFTD.Kb.GameTheoryEconomics.Ef1costShift
import AFTD.Kb.GameTheoryEconomics.Ef1costSocialCostEq
import AFTD.Kb.GameTheoryEconomics.IsEf1Chores
import AFTD.Kb.GameTheoryEconomics.SocialCost

/-!
# ef1cost_from_core

Topic: fair_division   Node: 27c879a9b041

From the core lemma to an EF1 allocation within `3 - 2√2` of the optimum.
-/

/-- From the core lemma to an EF1 allocation within `3 - 2√2` of the optimum. -/
lemma ef1cost_from_core {m : ℕ} (c : Fin 2 → Fin m → ℝ) (p q : Fin 2) (hpq : p ≠ q)
    (X : Finset (Fin m)) (hopt : ∀ τ : Fin m → Fin 2, ∑ j, c (if j ∈ X then p else q) j ≤ ∑ j, c (τ j) j)
    (hcore : ∃ Y : Finset (Fin m), X ⊆ Y ∧ ef1cost_pair_ok (c p) Y Yᶜ ∧
      ef1cost_pair_ok (c q) Yᶜ Y ∧ ∑ j ∈ Y \ X, (c p j - c q j) ≤ 3 - 2 * Real.sqrt 2) :
    ∃ σ, is_ef1_chores c σ ∧ ∀ τ, social_cost c σ ≤ social_cost c τ + (3 - 2 * Real.sqrt 2) := by
  obtain ⟨Y, hXY, hp, hq, hcost⟩ := hcore
  refine ⟨fun j => if j ∈ Y then p else q, ef1cost_ef1_of_pair c p q hpq Y hp hq, fun τ => ?_⟩
  rw [ef1cost_social_cost_eq, ef1cost_social_cost_eq, ef1cost_shift c p q X Y hXY]
  linarith [hopt τ]
