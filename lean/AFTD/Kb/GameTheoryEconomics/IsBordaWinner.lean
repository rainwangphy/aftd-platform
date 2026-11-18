import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BordaScore

/-!
# is_borda_winner

Topic: social_choice   Node: 5ba130522757

Provenance: formalization of a published result. Source: Gehrlein and Fishburn (1978)

In an election with k voters and n candidates with preference profile P : Fin k → Equiv.Perm (Fin n), candidate c : Fin n is a Borda winner if the Borda score of c is at least the Borda score of every candidate y : Fin n.
-/

/-- A candidate is a Borda winner if their Borda score is at least that of every other candidate. -/
def is_borda_winner (k n : ℕ) (P : Fin k → Equiv.Perm (Fin n)) (c : Fin n) : Prop := ∀ y : Fin n, borda_score k n P y ≤ borda_score k n P c
