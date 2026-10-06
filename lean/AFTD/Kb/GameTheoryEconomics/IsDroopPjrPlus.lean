import AFTD.Prelude

/-!
# is_droop_pjr_plus

Topic: social_choice   Node: d78de85480db

Provenance: formalization of a published result. Source: Justified Representation: From Hare to Droop, arXiv:2508.00811, Def. 11 (Droop-PJR+)

Droop-PJR+ (arXiv:2508.00811, Def. 11): for every ℓ ∈ [k], every group S with |S| > ℓn/(k+1) jointly approving a candidate outside W collectively approves at least ℓ members of W.
-/

/-- Droop-PJR+ (arXiv:2508.00811, Def. 11): for every `ℓ ∈ [k]`, every group `S` with `|S| > ℓ n/(k+1)` that jointly approves a candidate outside `W` collectively approves at least `ℓ` members of `W`. -/
def is_droop_pjr_plus {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ) (W : Finset (Fin m)) :
    Prop :=
  ∀ ℓ, 1 ≤ ℓ → ℓ ≤ k → ∀ S : Finset (Fin n), ℓ * n < (k + 1) * S.card →
    (∃ c, c ∉ W ∧ ∀ i ∈ S, c ∈ A i) → ℓ ≤ (W.filter fun c => ∃ i ∈ S, c ∈ A i).card
