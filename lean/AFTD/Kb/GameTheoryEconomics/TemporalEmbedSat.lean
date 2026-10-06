import AFTD.Prelude

/-!
# temporal_embed_sat

Topic: social_choice   Node: 87a60715722d

Provenance: formalization of a published result. Source: arXiv:2505.22513, App. A (satisfaction in the general-approval embedding)

Satisfaction of voter i from a set Y of (candidate, round) pairs: the number of pairs (c, r) in Y with c approved by i in round r.
-/

/-- Satisfaction of voter `i` from a set `Y` of (candidate, round) pairs: the number of pairs `(c, r) ∈ Y` with `c ∈ a i r`. -/
def temporal_embed_sat {n ℓ m : ℕ} (a : Fin n → Fin ℓ → Finset (Fin m)) (i : Fin n)
    (Y : Finset (Fin m × Fin ℓ)) : ℕ :=
  (Y.filter fun p => p.1 ∈ a i p.2).card
