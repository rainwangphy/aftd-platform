import AFTD.Prelude

/-!
# is_line_distance_preference_profile

Topic: social_choice   Node: ce0f962ea96f

Provenance: formalization of a published result. Source: arXiv:2611.05777 (Sublinear Metric Distortion for Matching), Sec. 1 and Sec. 6: one-sided matching of n agents to n items with ordinal rankings by distance; the probabilistic serial rule (agents rank items by distance), specialised to the real line

There are n agents and n items, both indexed by {0, ..., n-1}; agent i sits at the real position a_i and item j at b_j. Each agent's ranking is given as a permutation pref i of {0, ..., n-1}, with pref i k the item agent i ranks k-th (so every item is ranked exactly once). The profile is a distance-ranking profile when, for every agent i and ranks k < k', the item ranked k is at most as far from a_i as the item ranked k': |a_i - b_{pref i k}| <= |a_i - b_{pref i k'}| (ties in distance may be ordered either way).
-/

/-- Agents at positions `a i` and items at positions `b j` on the real line (both indexed by `Fin n`); each agent's ranking is a permutation `pref i`, with `pref i k` her `k`-th item, and it lists items by non-decreasing distance, ties broken arbitrarily. -/
def is_line_distance_preference_profile {n : ℕ} (a b : Fin n → ℝ) (pref : Fin n → Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, ∀ k k' : Fin n, k < k' → |a i - b (pref i k)| ≤ |a i - b (pref i k')|
