import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TemporalEmbedSat
import AFTD.Kb.GameTheoryEconomics.IsBfjrCohesive

/-!
# is_temporal_bfjr

Topic: social_choice   Node: 90061f728c39

Provenance: formalization of a published result. Source: arXiv:2505.22513, Def. A.5 (BFJR)

BFJR for a temporal outcome o (arXiv:2505.22513, Def. A.5): every (α, β)-BFJR-cohesive group has a member with satisfaction at least β from W = {(o(r), r)}.
-/

/-- BFJR for the outcome `o` of a temporal election (Def. A.5 in the embedding): every `(α, β)`-BFJR-cohesive group has a member whose satisfaction from `W = {(o r, r)}` is at least `β`. -/
def is_temporal_bfjr {n ℓ m : ℕ} (a : Fin n → Fin ℓ → Finset (Fin m)) (o : Fin ℓ → Fin m) :
    Prop :=
  ∀ (S : Finset (Fin n)) (α β : ℕ), is_bfjr_cohesive a S α β →
    ∃ i ∈ S, β ≤ temporal_embed_sat a i (Finset.univ.image fun r => (o r, r))
