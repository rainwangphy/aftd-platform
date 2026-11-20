import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.MatchableSubsetEvenOnForcedBridgeSides
import AFTD.Kb.Tcs.FactorcriticalFirstBridgeSecondShoreDoesNotCross
import AFTD.Kb.Tcs.FactorcriticalCrossingEvenShoreCoversOppositeFirstSide

/-!
# factorcritical_bridge_shores_force_endpoint_cover

Topic: graphs   Node: dcfc33710894

Provenance: helper lemma. OP-1957 uniform two-hub endpoint-cover reduction.

In the factor-critical first-bridge configuration, each later matched bridge witness has its external endpoint adjacent in the complement to an endpoint of the first bridge.
-/

theorem factorcritical_bridge_shores_force_endpoint_cover
    (k d : ℕ) (H : SimpleGraph (Fin (2*k+d+3))) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical Hᶜ (2*k)) (x y u v z : Fin (2*k+d+3))
    (hxy : x ≠ y) (huv : ¬ H.Adj u v)
    (hcommon : ∀ a, H.Adj u a → H.Adj v a → a = x ∨ a = y)
    (A B Q W : Finset (Fin (2*k+d+3))) (hAB : Disjoint A B)
    (hxu : x ∉ A ∪ B) (hyu : y ∉ A ∪ B) (hqx : x ∉ Q) (hqy : y ∉ Q)
    (hu : u ∈ A) (hv : v ∈ B)
    (hcut : ∀ a ∈ A, ∀ b ∈ B, (a ≠ u ∨ b ≠ v) → H.Adj a b)
    (hwsub : W ⊆ A ∪ B) (hwne : W.Nonempty) (hqne : Q.Nonempty)
    (hsize : Q.card + W.card = d+1)
    (hxyW : ∀ w ∈ W, H.Adj x w ∧ H.Adj y w)
    (hcross : ∀ q ∈ Q, ∀ w ∈ W, H.Adj q w)
    (hzQ : ∀ q ∈ Q, H.Adj z q)
    (hmatch : ∃ P : ((Hᶜ).induce {a | a ∈ W}).Subgraph, P.IsPerfectMatching) :
    H.Adj u z ∨ H.Adj v z := by
  classical
  have havoid : u ∉ W ∨ v ∉ W := by
    by_contra h
    have huW : u ∈ W := by tauto
    have hvW : v ∈ W := by tauto
    obtain ⟨q,hq⟩ := hqne
    rcases hcommon q (hcross q hq u huW).symm (hcross q hq v hvW).symm with h | h
    · exact hqx (h ▸ hq)
    · exact hqy (h ▸ hq)
  have hcutG : ∀ a ∈ A, ∀ b ∈ B, (Hᶜ).Adj a b → a = u ∧ b = v := by
    intro a ha b hb hab
    by_contra h
    have hn : a ≠ u ∨ b ≠ v := by tauto
    exact hab.2 (hcut a ha b hb hn)
  obtain ⟨heA,heB⟩ := matchable_subset_even_on_forced_bridge_sides Hᶜ A B W u v hAB hwsub hu hv hcutG havoid hmatch
  have hnoncross := factorcritical_first_bridge_second_shore_does_not_cross k d H hcrit x y u v hxy huv hcommon A B Q W hAB hxu hyu hqx hqy hu hv hcut hwsub hwne hqne heA heB hsize hxyW hcross
  have hcut' : ∀ b ∈ B, ∀ a ∈ A, (b ≠ v ∨ a ≠ u) → H.Adj b a := by
    intro b hb a ha h
    apply (hcut a ha b hb ?_).symm
    tauto
  rcases hnoncross with hWA | hWB
  · obtain ⟨w,hw⟩ := hwne
    have hwA : w ∉ A := fun h => (Finset.disjoint_left.mp hWA) hw h
    have hwB : w ∈ B := (Finset.mem_union.mp (hwsub hw)).resolve_left hwA
    have hne : (W ∩ B).Nonempty := ⟨w,Finset.mem_inter.mpr ⟨hw,hwB⟩⟩
    have hcoverA := factorcritical_crossing_even_shore_covers_opposite_first_side k d H hcrit x y v u hxy B A Q W hAB.symm
      (by simpa [Finset.union_comm] using hxu) (by simpa [Finset.union_comm] using hyu)
      hqx hqy hv hu hcut' (by simpa [Finset.union_comm] using hwsub) heB hne hsize hxyW hcross
    have huQ : u ∈ Q := by
      rcases Finset.mem_union.mp (hcoverA hu) with huW | huQ
      · exact ((Finset.disjoint_left.mp hWA) huW hu).elim
      · exact huQ
    exact Or.inl (hzQ u huQ).symm
  · obtain ⟨w,hw⟩ := hwne
    have hwB : w ∉ B := fun h => (Finset.disjoint_left.mp hWB) hw h
    have hwA : w ∈ A := (Finset.mem_union.mp (hwsub hw)).resolve_right hwB
    have hne : (W ∩ A).Nonempty := ⟨w,Finset.mem_inter.mpr ⟨hw,hwA⟩⟩
    have hcoverB := factorcritical_crossing_even_shore_covers_opposite_first_side k d H hcrit x y u v hxy A B Q W hAB hxu hyu hqx hqy hu hv hcut hwsub heA hne hsize hxyW hcross
    have hvQ : v ∈ Q := by
      rcases Finset.mem_union.mp (hcoverB hv) with hvW | hvQ
      · exact ((Finset.disjoint_left.mp hWB) hvW hv).elim
      · exact hvQ
    exact Or.inr (hzQ v hvQ).symm
