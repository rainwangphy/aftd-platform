import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.ComplementAdjacentTwinsHaveEqualOpenNeighbors
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual
import AFTD.Kb.Tcs.FactorcriticalFalseTwinForcedBridgeResidualShores
import AFTD.Kb.Tcs.FactorcriticalInduceOneAfterVertexRestriction
import AFTD.Kb.Tcs.NontrivialFactorcriticalGraphConnected
import AFTD.Kb.Tcs.FactorCriticalAnticompleteCutSideEven
import AFTD.Kb.Tcs.CrossingShoresForceTwoCommonOppositeVertices
import AFTD.Kb.Tcs.CrossingBridgeShoresForceCutEquality
import AFTD.Kb.Tcs.D11LargeBridgeFamilyForcesFourShore
import AFTD.Kb.Tcs.FactorcriticalSeparatorLowerBound
import AFTD.Kb.Tcs.FactorcriticalCrossingShoreIntersectionEven
import AFTD.Kb.Tcs.TwoFourShoresExternalOppositeImpossible
import AFTD.Kb.Tcs.FourShoreForcesOtherOppositeAvoidsShore
import AFTD.Kb.Tcs.FourShoreEvenCrossingIsContained
import AFTD.Kb.Tcs.CompleteBipartiteInternalWalkCharge
import AFTD.Kb.Tcs.InternalNeighborDegreeBudget
import AFTD.Kb.Tcs.ExternalNeighborCountWithRInternal
import AFTD.Kb.Tcs.ChooseExternalNonNeighborPadding
import AFTD.Kb.Tcs.BridgeFamilyVariableExternalIncidenceBudget
import AFTD.Kb.Tcs.BridgeFamilyHasNoFullFirstNeighborhoodShore
import AFTD.Kb.Tcs.D11AllOppositeShoresCannotBeDisjoint
import AFTD.Kb.Tcs.D11FourShoreHasAtMostTwoInternalOppositeVertices
import AFTD.Kb.Tcs.FactorcriticalMinimalD11Kge9ExcludesSaturatedTwins

/-!
# factorcritical_minimal_d11_k9_excludes_saturated_twins

Topic: graphs   Node: 34982c4b7cc2

Provenance: helper lemma. https://arxiv.org/abs/2611.22690; the saturated complement-twin branch of OP-1957.

At k=9 and complement maximum degree eleven, the displayed saturated adjacent complement twins cannot occur in a minimally k-extendible 2k-factor-critical graph.
-/

-- no helper declarations: the k = 9 instance of the general theorem

theorem factorcritical_minimal_d11_k9_excludes_saturated_twins
    (H : SimpleGraph (Fin (2*9+11+3))) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical Hᶜ (2*9)) (hmin : is_minimally_k_extendable Hᶜ 9)
    (x y : Fin (2*9+11+3)) (hxy : H.Adj x y)
    (hxdeg : (H.neighborFinset x).card = 11) (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (htwin : ∀ a, a ≠ x → a ≠ y → (H.Adj x a ↔ H.Adj y a)) : False := by
  exact factorcritical_minimal_d11_kge9_excludes_saturated_twins 9 le_rfl H hcrit hmin x y hxy hxdeg hmax htwin
