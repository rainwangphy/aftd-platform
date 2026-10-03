import AFTD.Prelude

/-!
# is_droop_fjr

Topic: social_choice   Node: f8410501bab3

Droop-FJR (Casey–Elkind, Def. 10): every Droop weakly (ℓ, T)-cohesive group (each member approves ≥ ℓ members of T and |S| > |T|n/(k+1)) has a member approving at least ℓ members of W.
-/

/-- Droop-FJR (Casey–Elkind, Def. 10): for every `ℓ ∈ [k]` and `T`, every Droop weakly `(ℓ, T)`-cohesive group (each member approves at least `ℓ` members of `T`, and `|S| > |T| n/(k+1)`) has a member approving at least `ℓ` members of `W`. -/
def is_droop_fjr {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ) (W : Finset (Fin m)) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ℓ ≤ k → ∀ (T : Finset (Fin m)) (S : Finset (Fin n)),
    (∀ i ∈ S, ℓ ≤ (A i ∩ T).card) → T.card * n < (k + 1) * S.card →
      ∃ i ∈ S, ℓ ≤ (A i ∩ W).card
