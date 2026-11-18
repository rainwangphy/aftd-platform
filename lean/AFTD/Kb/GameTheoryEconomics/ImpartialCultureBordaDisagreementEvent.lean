import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetWinner
import AFTD.Kb.GameTheoryEconomics.BordaScore
import AFTD.Kb.GameTheoryEconomics.IsBordaWinner

/-!
# impartial_culture_borda_disagreement_event

Topic: social_choice   Node: 8a8c5b38fcff

Provenance: formalization of a published result. Source: Gehrlein and Fishburn (1978)

The event D_{k,n} under impartial culture with k voters and n candidates that there exists a candidate w : Fin n who is the strict Condorcet winner (beating every other candidate pairwise) and yet w is not a Borda winner.
-/

/-- Event D_{k,n} that there exists a strict Condorcet winner who is not a Borda winner. -/
def impartial_culture_borda_disagreement_event (k n : ℕ) (P : Fin k → Equiv.Perm (Fin n)) : Prop := ∃ w : Fin n, condorcet_winner (fun (v : Fin k) (x y : Fin n) => P v x < P v y) w ∧ ¬ is_borda_winner k n P w
