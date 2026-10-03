import AFTD.Prelude

/-!
# plackett_luce_prob

Topic: social_choice   Node: 616cfc7d51ba

Plackett-Luce probability of a ranking (best first): the product over positions of the weight of the alternative placed there divided by the total weight of it and all alternatives ranked below it.
-/

/-- Plackett–Luce probability of the ranking `l` (best first) under weights `w`: the product over positions of `w a / (w a + total weight of the alternatives below a)`. -/
noncomputable def plackett_luce_prob (w : ℕ → ℝ) (l : List ℕ) : ℝ := match l with
  | [] => 1
  | a :: t => w a / (w a + (t.map w).sum) * plackett_luce_prob w t
