import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPositionalScoringVector
import AFTD.Kb.GameTheoryEconomics.ScoringNormOne
import AFTD.Kb.GameTheoryEconomics.ScoringLast

/-!
# rank_score_veto_core_score_norm_sub_last_ge_one

Topic: social_choice   Node: 31e7e4d8b423

Provenance: helper lemma. step towards rank_score_veto_core_tightness_conjecture

For a positional scoring vector s on Fin m with m at least 3, the 1-norm of s minus the last-place score is at least 1 (hence nonnegative).
-/

/-- A positional scoring vector with at least 3 candidates has ||s||_1 - s_last at least 1 (in particular nonnegative). -/
theorem rank_score_veto_core_score_norm_sub_last_ge_one :
    ∀ (C : Type*) [Fintype C] (hm : 3 ≤ Fintype.card C)
      (s : Fin (Fintype.card C) → ℚ) (hs : is_positional_scoring_vector (Fintype.card C) s),
      (1 : ℚ) ≤ scoring_norm_one s - scoring_last (Fintype.card C) (by omega) s := by
  intro C _ hm s hs
  dsimp [scoring_norm_one, scoring_last]
  have hm0 : 0 < Fintype.card C := by omega
  have hmlast : Fintype.card C - 1 < Fintype.card C := by omega
  have h_ne : (⟨0, hm0⟩ : Fin (Fintype.card C)) ≠ ⟨Fintype.card C - 1, hmlast⟩ := by
    intro h
    have : 0 = Fintype.card C - 1 := Fin.mk.inj h
    omega
  have h_pair : ∑ i ∈ ({⟨0, hm0⟩, ⟨Fintype.card C - 1, hmlast⟩} : Finset (Fin (Fintype.card C))), s i =
      s ⟨0, hm0⟩ + s ⟨Fintype.card C - 1, hmlast⟩ :=
    Finset.sum_pair h_ne
  have h_sub : ({⟨0, hm0⟩, ⟨Fintype.card C - 1, hmlast⟩} : Finset (Fin (Fintype.card C))) ⊆ Finset.univ :=
    Finset.subset_univ _
  have h_le : ∑ i ∈ ({⟨0, hm0⟩, ⟨Fintype.card C - 1, hmlast⟩} : Finset (Fin (Fintype.card C))), s i ≤
      ∑ i : Fin (Fintype.card C), s i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h_sub
    intro i _ _
    exact hs.2.1 i
  rcases hs.2.2 with ⟨h0, hs0⟩
  have h_s0 : s ⟨0, hm0⟩ = 1 := by
    have : (⟨0, hm0⟩ : Fin (Fintype.card C)) = ⟨0, h0⟩ := rfl
    rw [this, hs0]
  have h_last : s ⟨Fintype.card C - 1, hmlast⟩ = s ⟨Fintype.card C - 1, by omega⟩ := rfl
  linarith
