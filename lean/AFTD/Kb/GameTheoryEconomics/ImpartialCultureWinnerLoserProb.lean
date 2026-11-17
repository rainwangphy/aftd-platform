import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetWinner
import AFTD.Kb.GameTheoryEconomics.CondorcetLoser
import AFTD.Kb.GameTheoryEconomics.ImpartialCultureProb

/-!
# impartial_culture_winner_loser_prob

Topic: social_choice   Node: 89e1a55c4cfa

Provenance: formalization of a published result. Source: Guilbaud 1952; Gehrlein & Fishburn 1976

For natural numbers k and n, impartial_culture_winner_loser_prob k n is the real probability under impartial culture that an election with k voters and n candidates has both a strict Condorcet winner and a strict Condorcet loser.
-/

/-- Probability that an impartial-culture election has both a strict Condorcet winner and a strict Condorcet loser. -/
noncomputable def impartial_culture_winner_loser_prob (k n : ℕ) : ℝ := open Classical in
  impartial_culture_prob k n (fun P =>
    (∃ w : Fin n, condorcet_winner (fun (v : Fin k) (x y : Fin n) => P v x < P v y) w) ∧
    (∃ l : Fin n, condorcet_loser (fun (v : Fin k) (x y : Fin n) => P v x < P v y) l))
