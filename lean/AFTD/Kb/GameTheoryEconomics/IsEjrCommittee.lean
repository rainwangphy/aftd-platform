import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCohesiveGroup

/-!
# is_ejr_committee

Topic: social_choice   Node: 75122a4375e1

Provenance: formalization of a published result. Source: arXiv:2007.01795 (Multi-Winner Voting with Approval Preferences), definition of EJR

A committee W with |W| = k satisfies EJR if for every ℓ ≥ 1 and every ℓ-cohesive group G some voter i ∈ G has |A_i ∩ W| ≥ ℓ.
-/

/-- Extended justified representation of a committee `W` of size `k`: for every `ℓ ≥ 1`, every `ℓ`-cohesive group has a member who approves at least `ℓ` members of `W`. -/
def is_ejr_committee {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ) (W : Finset (Fin m)) :
    Prop :=
  W.card = k ∧ ∀ ℓ, 1 ≤ ℓ → ∀ G : Finset (Fin n), is_ejr_cohesive_group A k ℓ G →
    ∃ i ∈ G, ℓ ≤ (A i ∩ W).card
