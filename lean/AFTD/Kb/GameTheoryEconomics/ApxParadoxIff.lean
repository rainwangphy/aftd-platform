import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PopulationParadox
import AFTD.Kb.GameTheoryEconomics.ApxParadox

/-!
# apx_paradox_iff

Topic: social_choice   Node: b47cbeb21799

A population paradox at a common house size is equivalent to the Boolean paradox test on the solution's seat vectors.
-/

lemma apx_paradox_iff (f : (Fin 4 → ℕ) → ℕ → (Fin 4 → ℕ)) (p q : Fin 4 → ℕ) (h : ℕ) :
    population_paradox f p q h h ↔ apx_paradox p (f p h) q (f q h) = true := by
  unfold population_paradox apx_paradox
  simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, j, hij, h1, h2, h3, h4⟩; exact ⟨i, j, ⟨⟨⟨⟨hij, h1⟩, h2⟩, h3⟩, h4⟩⟩
  · rintro ⟨i, j, ⟨⟨⟨⟨hij, h1⟩, h2⟩, h3⟩, h4⟩⟩; exact ⟨i, j, hij, h1, h2, h3, h4⟩
