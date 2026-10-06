import AFTD.Prelude

/-!
# temporal_feasible

Topic: social_choice   Node: a420c6c76480

Provenance: formalization of a published result. Source: arXiv:2505.22513, App. A (general-approval embedding of a temporal election: feasible sets of (candidate, round) pairs)

A set of (candidate, round) pairs is feasible in the general-approval embedding of a temporal election if it uses every round at most once.
-/

/-- Feasibility in the general-approval embedding of a temporal election: a set of (candidate, round) pairs is feasible if it uses each round at most once. -/
def temporal_feasible {ℓ m : ℕ} (X : Finset (Fin m × Fin ℓ)) : Prop :=
  ∀ p ∈ X, ∀ q ∈ X, p.2 = q.2 → p.1 = q.1
