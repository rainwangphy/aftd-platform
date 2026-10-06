import AFTD.Prelude

/-!
# is_ejr_cohesive_group

Topic: social_choice   Node: f09b714f1888

Provenance: formalization of a published result. Source: arXiv:2007.01795 (Multi-Winner Voting with Approval Preferences), definition of ℓ-cohesive groups (Sec. on proportionality axioms); division cleared as ℓ·n ≤ |G|·k

For committee size k, a group G of the n voters is ℓ-cohesive if |G| ≥ ℓ·n/k and |∩_{i∈G} A_i| ≥ ℓ.
-/

/-- A group `G` of voters is `ℓ`-cohesive for committee size `k` in the approval profile `A` (voters `Fin n`, candidates `Fin m`): `|G| ≥ ℓ n / k` and the members of `G` jointly approve at least `ℓ` candidates. -/
def is_ejr_cohesive_group {n m : ℕ} (A : Fin n → Finset (Fin m)) (k ℓ : ℕ)
    (G : Finset (Fin n)) : Prop :=
  ℓ * n ≤ G.card * k ∧ ℓ ≤ (Finset.univ.filter fun c => ∀ i ∈ G, c ∈ A i).card
