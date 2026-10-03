import AFTD.Prelude

/-!
# is_droop_ejr_plus

Topic: social_choice   Node: 06b3b81b1e2e

Droop-EJR+ (Casey–Elkind, Def. 12): for every ℓ ∈ [k], every group S with |S| > ℓn/(k+1) jointly approving a candidate outside W has a member approving at least ℓ members of W.
-/

/-- Droop-EJR+ (Casey–Elkind, Def. 12): for every `ℓ ∈ [k]`, every group `S` with `|S| > ℓ n/(k+1)` that jointly approves a candidate outside `W` has a member approving at least `ℓ` members of `W`. -/
def is_droop_ejr_plus {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ) (W : Finset (Fin m)) :
    Prop :=
  ∀ ℓ, 1 ≤ ℓ → ℓ ≤ k → ∀ S : Finset (Fin n), ℓ * n < (k + 1) * S.card →
    (∃ c, c ∉ W ∧ ∀ i ∈ S, c ∈ A i) → ∃ i ∈ S, ℓ ≤ (A i ∩ W).card
