import AFTD.Prelude

/-!
# temporal_sat

Topic: social_choice   Node: 2d6b8c93695a

Satisfaction of voter i in a temporal election from outcome o restricted to rounds R: the number of rounds r in R with o(r) approved by i in round r.
-/

/-- Satisfaction of voter `i` in a temporal election with ballots `a` (voter `i` approves `a i r` in round `r`) from the outcome `o` restricted to the rounds `R`: the number of rounds `r ∈ R` in which `o r ∈ a i r`. -/
def temporal_sat {n ℓ m : ℕ} (a : Fin n → Fin ℓ → Finset (Fin m)) (i : Fin n)
    (o : Fin ℓ → Fin m) (R : Finset (Fin ℓ)) : ℕ :=
  (R.filter fun r => o r ∈ a i r).card
