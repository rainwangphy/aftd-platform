import AFTD.Prelude

/-!
# impartial_culture_prob

Topic: social_choice   Node: cf2f5a28fbdb

Provenance: formalization of a published result. Source: Guilbaud 1952; Gehrlein & Fishburn 1976

Given natural numbers k and n, and a predicate E on profiles Fin k → Equiv.Perm (Fin n), impartial_culture_prob k n E is the real number defined as the cardinality of the set of profiles satisfying E divided by the total number of profiles in Fin k → Equiv.Perm (Fin n).
-/

/-- The real-valued uniform probability of an event on preference profiles under impartial culture. -/
noncomputable def impartial_culture_prob (k n : ℕ)
    (E : (Fin k → Equiv.Perm (Fin n)) → Prop) : ℝ := open Classical in
  ((Finset.univ.filter E).card : ℝ) / (Fintype.card (Fin k → Equiv.Perm (Fin n)) : ℝ)
