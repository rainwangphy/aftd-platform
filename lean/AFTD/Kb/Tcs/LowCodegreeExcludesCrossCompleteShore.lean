import AFTD.Prelude

/-!
# low_codegree_excludes_cross_complete_shore

Topic: graphs   Node: d16ee909848e

Provenance: helper lemma. Bridge-to-crossing-set verification for the OP-1957 campaign.

If W has at least two neighbors of x and every vertex of Q is adjacent to all of W, then a vertex z with at most one common neighbor with x cannot belong to Q.
-/

theorem low_codegree_excludes_cross_complete_shore
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x z : V) (W Q : Finset V)
    (hW : W ⊆ H.neighborFinset x) (hsize : 2 ≤ W.card)
    (hcodeg : ((H.neighborFinset x).filter (fun w => H.Adj z w)).card ≤ 1)
    (hcross : ∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) : z ∉ Q := by
  intro hz
  have hsub : W ⊆ (H.neighborFinset x).filter (fun w => H.Adj z w) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨hW hw, hcross z hz w hw⟩
  have := Finset.card_le_card hsub
  omega
