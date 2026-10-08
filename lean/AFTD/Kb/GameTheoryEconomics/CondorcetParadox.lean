import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetWinner

/-!
# condorcet_paradox

Topic: social_choice   Node: 12e7f26f3c1f

Provenance: formalization of a published result. Source: Condorcet 1785, Essai sur l'application de l'analyse à la probabilité des décisions rendues à la pluralité des voix

The Condorcet paradox: there exists a preference profile of 3 voters over 3 alternatives, where each voter has a strict linear order of preferences, such that no alternative is a Condorcet winner.
-/

def condorcet_paradox_score : Fin 3 → Fin 3 → ℕ
  | 0, 0 => 2
  | 0, 1 => 1
  | 0, 2 => 0
  | 1, 1 => 2
  | 1, 2 => 1
  | 1, 0 => 0
  | 2, 2 => 2
  | 2, 0 => 1
  | 2, 1 => 0

def condorcet_paradox_pref (v : Fin 3) (x y : Fin 3) : Prop :=
  condorcet_paradox_score v x > condorcet_paradox_score v y

instance condorcet_paradox_decidable_rel (v : Fin 3) :
    DecidableRel (condorcet_paradox_pref v) := by
  intro x y
  unfold condorcet_paradox_pref
  infer_instance

theorem condorcet_paradox_strict_order (v : Fin 3) :
    IsStrictTotalOrder (Fin 3) (condorcet_paradox_pref v) where
  trichotomous := by
    revert v
    decide
  irrefl := by
    revert v
    decide
  trans := by
    revert v
    decide

theorem condorcet_paradox_no_winner (x : Fin 3) :
    ¬ condorcet_winner condorcet_paradox_pref x := by
  intro h
  unfold condorcet_winner at h
  revert x h
  decide

/-- The Condorcet paradox: there exists an election with 3 voters and 3 candidates with strict linear preferences admitting no Condorcet winner. -/
theorem condorcet_paradox :
    ∃ (P : Fin 3 → Fin 3 → Fin 3 → Prop) (_ : ∀ v, DecidableRel (P v)),
      (∀ v, IsStrictTotalOrder (Fin 3) (P v)) ∧ ∀ x : Fin 3, ¬ condorcet_winner P x := by
  refine ⟨condorcet_paradox_pref, condorcet_paradox_decidable_rel,
          condorcet_paradox_strict_order, condorcet_paradox_no_winner⟩
