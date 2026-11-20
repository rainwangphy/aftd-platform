import AFTD.Prelude
import AFTD.Kb.Tcs.FactorcriticalBridgeShoresForceEndpointCover
import AFTD.Kb.Tcs.SaturatedFirstBridgeExternalEndpointCount
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# factorcritical_bridge_family_endpoint_bound

Topic: graphs   Node: a2685bf4b770

Provenance: helper lemma. OP-1957 uniform bridge-family endpoint bound.

A family of factor-critical matched bridge witnesses has at most |A|+|B| external endpoints under the first-bridge hypotheses.
-/

theorem factorcritical_bridge_family_endpoint_bound
    (k d : ℕ) (H : SimpleGraph (Fin (2*k+d+3))) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical Hᶜ (2*k)) (x y u v : Fin (2*k+d+3))
    (hxy : x ≠ y) (huv : ¬ H.Adj u v)
    (hcommon : ∀ a, H.Adj u a → H.Adj v a → a = x ∨ a = y)
    (A B C : Finset (Fin (2*k+d+3))) (hAB : Disjoint A B) (hu : u ∈ A) (hv : v ∈ B)
    (hxu : x ∉ A ∪ B) (hyu : y ∉ A ∪ B) (hxC : x ∉ C) (hyC : y ∉ C)
    (hCS : Disjoint C (A ∪ B)) (hsize : A.card + B.card + 1 = d)
    (hxyA : ∀ a ∈ A ∪ B, H.Adj a x ∧ H.Adj a y)
    (hcut : ∀ a ∈ A, ∀ b ∈ B, (a ≠ u ∨ b ≠ v) → H.Adj a b)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (hfamily : ∀ z ∈ C, ∃ Q W : Finset (Fin (2*k+d+3)),
      x ∉ Q ∧ y ∉ Q ∧ W ⊆ A ∪ B ∧ W.Nonempty ∧ Q.Nonempty ∧ Q.card + W.card = d+1 ∧
      (∀ w ∈ W, H.Adj x w ∧ H.Adj y w) ∧
      (∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) ∧ (∀ q ∈ Q, H.Adj z q) ∧
      ∃ P : ((Hᶜ).induce {a | a ∈ W}).Subgraph, P.IsPerfectMatching) :
    C.card ≤ A.card + B.card := by
  classical
  apply saturated_first_bridge_external_endpoint_count H d x y u v hxy A B C hAB hu hv hxu hyu hxC hyC hCS hsize hxyA hcut hmax
  intro z hz
  obtain ⟨Q,W,hqx,hqy,hwsub,hwne,hqne,hqsize,hxyW,hcross,hzQ,hmatch⟩ := hfamily z hz
  exact factorcritical_bridge_shores_force_endpoint_cover k d H hcrit x y u v z hxy huv hcommon A B Q W hAB hxu hyu hqx hqy hu hv hcut hwsub hwne hqne hqsize hxyW hcross hzQ hmatch
