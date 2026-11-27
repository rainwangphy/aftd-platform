import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteSubsetHasMaximumMatching
import AFTD.Kb.Tcs.ExtendibleBalancedCutMatchingSymmetryOfIndependence
import AFTD.Kb.Tcs.ExtendibleEqualCutMaximumMatchingDeficiencyAtMostOne
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleIndependentCommonNonneighborDeficitLeOne

/-!
# extendible_common_nonneighbor_deficit_equality_matchable

Topic: graphs   Node: fa1169642a8b

Provenance: helper lemma. Positive-separator transfer for OP-1957; https://arxiv.org/abs/2611.22690.

Under the stated high-degree extendibility and independence assumptions, if an independent U with at least two vertices is anticomplete to disjoint W and 2|U|+|W|=2k+2, then G[W] has a perfect matching.
-/

theorem extendible_common_nonneighbor_deficit_equality_matchable
    (k : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hdegree : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card)
    (hind : ∀ I : Finset (Fin (4*k)),
      (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) → I.card ≤ k)
    (U W : Finset (Fin (4*k))) (hdis : Disjoint U W) (hU : 2 ≤ U.card)
    (hUind : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v)
    (hanti : ∀ u ∈ U, ∀ w ∈ W, ¬ G.Adj u w)
    (hequality : 2*U.card+W.card = 2*k+2) :
    ∃ P : (G.induce {v | v ∈ W}).Subgraph, P.IsPerfectMatching := by
  have hU_nonempty : U.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    norm_num at hU
  have hle := extendible_independent_common_nonneighbor_deficit_le_one k G hext hdegree hind U W hdis hU_nonempty hUind hanti
  omega
