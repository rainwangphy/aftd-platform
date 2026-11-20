import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.FactorcriticalSaturatedTwinsNotAllIncidentEdgesHaveForcedResiduals
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual

/-!
# factorcritical_saturated_twin_first_forced_edge_removable_extended_order

Topic: graphs   Node: d942e13ca9f8

Provenance: helper lemma. OP-1957 equality-twin removable-edge branch, with the order restriction weakened by the endpoint count.

The saturated-twin factor-critical first-witness configuration has a removable edge when d≤2k+2.
-/

theorem factorcritical_saturated_twin_first_forced_edge_removable_extended_order (k d : ℕ) (H : SimpleGraph (Fin (2*k+d+3))) [DecidableRel H.Adj] (hcrit : is_k_factor_critical Hᶜ (2*k)) (hext : is_k_extendable Hᶜ k) (x y u v : Fin (2*k+d+3)) (hxy : H.Adj x y) (hxdeg : (H.neighborFinset x).card = d) (hmax : ∀ a, (H.neighborFinset a).card ≤ d) (htwin : ∀ a, a ≠ x → a ≠ y → (H.Adj x a ↔ H.Adj y a)) (hu : u ∈ (H.neighborFinset x).erase y) (hv : v ∈ (H.neighborFinset x).erase y) (huv : (Hᶜ).Adj u v) (hcommon : ∀ a, H.Adj u a → H.Adj v a → a = x ∨ a = y) (hmatch : ∃ P : ((Hᶜ).induce {a | a ∈ (H.neighborFinset x).erase y}).Subgraph, P.IsPerfectMatching ∧ P.Adj ⟨u,hu⟩ ⟨v,hv⟩) (hforced : ∀ P : ((Hᶜ).induce {a | a ∈ (H.neighborFinset x).erase y}).Subgraph, P.IsPerfectMatching → P.Adj ⟨u,hu⟩ ⟨v,hv⟩) (horder : d ≤ 2*k+2) : ∃ z, (Hᶜ).Adj x z ∧ is_k_extendable ((Hᶜ).deleteEdges {s(x,z)}) k := by
  classical
  by_contra hnot
  obtain ⟨z,hxz,hno⟩ := factorcritical_saturated_twins_not_all_incident_edges_have_forced_residuals
    k d H hcrit x y u v hxy hxdeg hmax htwin hu hv huv hcommon hmatch hforced horder
  have hessential : ¬ is_k_extendable ((Hᶜ).deleteEdges {s(x,z)}) k := by
    intro he
    exact hnot ⟨z,hxz,he⟩
  obtain ⟨R,hR,hx,hz,hPM,hforcedR⟩ := k_extendable_essential_edge_has_forced_matching_residual
    (2*k+d+3) k Hᶜ x z hxz hext hessential
  apply hno
  refine ⟨R, ?_, hx, hz, hPM, hforcedR⟩
  omega
