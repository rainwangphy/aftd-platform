import AFTD.Prelude

/-!
# is_droop_jr

Topic: social_choice   Node: ab11ca9a54de

Provenance: formalization of a published result. Source: Justified Representation: From Hare to Droop, arXiv:2508.00811, Sec. 2 (Droop-JR)

Droop-JR: every group S of voters with |S| > n/(k+1) that jointly approves some candidate contains a voter who approves some member of W.
-/

/-- Droop-JR (arXiv:2508.00811): every group of more than `n/(k+1)` voters with a commonly approved candidate has a member who approves some member of `W`. -/
def is_droop_jr {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ) (W : Finset (Fin m)) : Prop :=
  ∀ S : Finset (Fin n), n < (k + 1) * S.card → (∃ c, ∀ i ∈ S, c ∈ A i) →
    ∃ i ∈ S, ∃ c ∈ W, c ∈ A i
