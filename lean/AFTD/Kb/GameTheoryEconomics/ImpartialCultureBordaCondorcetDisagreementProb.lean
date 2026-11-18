import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ImpartialCultureProb
import AFTD.Kb.GameTheoryEconomics.ImpartialCultureWinnerProb
import AFTD.Kb.GameTheoryEconomics.ImpartialCultureBordaDisagreementEvent

/-!
# impartial_culture_borda_condorcet_disagreement_prob

Topic: social_choice   Node: 5b864db07ae4

Provenance: formalization of a published result. Source: Gehrlein and Fishburn (1978)

Under impartial culture with k voters and n candidates, the conditional probability that the strict Condorcet winner is not a Borda winner given that a strict Condorcet winner exists, defined as the probability of impartial_culture_borda_disagreement_event k n divided by impartial_culture_winner_prob k n.
-/

/-- The conditional probability P(D_{k,n} | E_{k,n}) that the Condorcet winner fails to be a Borda winner under impartial culture. -/
noncomputable def impartial_culture_borda_condorcet_disagreement_prob (k n : ℕ) : ℝ := impartial_culture_prob k n (impartial_culture_borda_disagreement_event k n) / impartial_culture_winner_prob k n
