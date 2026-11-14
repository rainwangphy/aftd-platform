import AFTD.Prelude

/-!
# is_uniform_bivalued_chores

Topic: fair_division   Node: a248108eb39f

Provenance: formalization of a published result. Source: OP-1697

A chore cost profile for two agents and m chores is uniform bivalued with ratio r if the first agent assigns cost 1 to every chore and the second agent assigns each chore cost either 1 or r.
-/

/-- A two-agent chore cost profile is uniform bivalued with ratio r if agent 0 assigns cost 1 to every chore and agent 1 assigns cost 1 or r to each chore. -/
def is_uniform_bivalued_chores {m : ℕ} (r : ℝ) (c : Fin 2 → Fin m → ℝ) : Prop := (∀ g, c 0 g = 1) ∧ (∀ g, c 1 g = 1 ∨ c 1 g = r)
