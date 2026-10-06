import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TemporalFeasible
import AFTD.Kb.GameTheoryEconomics.TemporalEmbedSat

/-!
# is_bfjr_cohesive

Topic: social_choice   Node: 3c09aa1c37bb

Provenance: formalization of a published result. Source: arXiv:2505.22513, Def. A.5 ((alpha, beta)-BFJR-cohesive groups)

(α, β)-BFJR-cohesiveness (arXiv:2505.22513, Def. A.5) in the embedding of a temporal election: for every feasible X, either some Y with |Y| = α giving every member of S satisfaction at least β has X ∪ Y feasible, or |S|/n > α/(|X| + α).
-/

/-- `(α, β)`-BFJR-cohesiveness (arXiv:2505.22513, Def. A.5) in the embedding of a temporal election: for every feasible `X`, either some `Y` with `|Y| = α`, giving every member of `S` satisfaction at least `β`, has `X ∪ Y` feasible, or `|S|/n > α/(|X| + α)`. -/
def is_bfjr_cohesive {n ℓ m : ℕ} (a : Fin n → Fin ℓ → Finset (Fin m)) (S : Finset (Fin n))
    (α β : ℕ) : Prop :=
  ∀ X : Finset (Fin m × Fin ℓ), temporal_feasible X →
    (∃ Y : Finset (Fin m × Fin ℓ), Y.card = α ∧ (∀ i ∈ S, β ≤ temporal_embed_sat a i Y) ∧
        temporal_feasible (X ∪ Y)) ∨
      α * n < S.card * (X.card + α)
