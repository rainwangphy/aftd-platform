import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.ForcedZeroCodegreeEdgePartitionOnFinset
import AFTD.Kb.Tcs.ComplementAdjacentTwinsHaveEqualOpenNeighbors
import AFTD.Kb.Tcs.FactorcriticalFalseTwinForcedBridgeResidualShores
import AFTD.Kb.Tcs.PerfectMatchingForcedEdgeInEveryMatching
import AFTD.Kb.Tcs.MatchedResidualBridgeShoreHasPerfectMatching
import AFTD.Kb.Tcs.FactorcriticalBridgeFamilyEndpointBound
import AFTD.Kb.Tcs.Op2037SubgraphFintype

/-!
# factorcritical_saturated_twins_not_all_incident_edges_have_forced_residuals

Topic: graphs   Node: 8a4ff109846f

Provenance: helper lemma. OP-1957 equality-twin branch, derived from the unrestricted bridge and crossing-cut reductions.

In the factor-critical saturated-twin first-witness configuration, an incident edge has no forced matching residual when d≤2k+2.
-/

theorem factorcritical_saturated_twins_not_all_incident_edges_have_forced_residuals
    (k d : ℕ) (H : SimpleGraph (Fin (2*k+d+3))) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical Hᶜ (2*k))
    (x y u v : Fin (2*k+d+3)) (hxy : H.Adj x y)
    (hxdeg : (H.neighborFinset x).card = d)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (htwin : ∀ a, a ≠ x → a ≠ y → (H.Adj x a ↔ H.Adj y a))
    (hu : u ∈ (H.neighborFinset x).erase y) (hv : v ∈ (H.neighborFinset x).erase y)
    (huv : (Hᶜ).Adj u v)
    (hcommon : ∀ a, H.Adj u a → H.Adj v a → a = x ∨ a = y)
    (hmatch : ∃ P : ((Hᶜ).induce {a | a ∈ (H.neighborFinset x).erase y}).Subgraph,
      P.IsPerfectMatching ∧ P.Adj ⟨u,hu⟩ ⟨v,hv⟩)
    (hforced : ∀ P : ((Hᶜ).induce {a | a ∈ (H.neighborFinset x).erase y}).Subgraph,
      P.IsPerfectMatching → P.Adj ⟨u,hu⟩ ⟨v,hv⟩) (horder : d ≤ 2*k+2) :
    ∃ z, (Hᶜ).Adj x z ∧ ¬ ∃ R : Finset (Fin (2*k+d+3)), R.card = d+3 ∧
      ∃ (hx : x ∈ R) (hz : z ∈ R),
        (∃ P : ((Hᶜ).induce {a | a ∈ R}).Subgraph, P.IsPerfectMatching) ∧
        ¬ ∃ P : (((Hᶜ).induce {a | a ∈ R}).deleteEdges
          {s(⟨x,hx⟩,⟨z,hz⟩)}).Subgraph, P.IsPerfectMatching := by
  classical
  by_contra hnot
  have hwitness : ∀ z, (Hᶜ).Adj x z → ∃ R : Finset (Fin (2*k+d+3)), R.card = d+3 ∧
      ∃ (hx : x ∈ R) (hz : z ∈ R),
        (∃ P : ((Hᶜ).induce {a | a ∈ R}).Subgraph, P.IsPerfectMatching) ∧
        ¬ ∃ P : (((Hᶜ).induce {a | a ∈ R}).deleteEdges
          {s(⟨x,hx⟩,⟨z,hz⟩)}).Subgraph, P.IsPerfectMatching := by
    intro z hz
    by_contra hn
    exact hnot ⟨z,hz,hn⟩
  let S := (H.neighborFinset x).erase y
  let C := (Hᶜ).neighborFinset x
  have hxS : x ∉ S := by simp [S]
  have hyS : y ∉ S := by simp [S]
  have hyN : y ∈ H.neighborFinset x := by simpa using hxy
  have hSsize : S.card + 1 = d := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hyN, hxdeg]
    have hdpos : 0 < d := by
      rw [← hxdeg]
      exact Finset.card_pos.mpr ⟨y,hyN⟩
    omega
  have hcoS : ∀ a ∈ S, ¬ (((Hᶜ)ᶜ).Adj u a ∧ ((Hᶜ)ᶜ).Adj v a) := by
    intro a ha h
    have hua : H.Adj u a := by simpa using h.1
    have hva : H.Adj v a := by simpa using h.2
    rcases hcommon a hua hva with h | h
    · exact hxS (h ▸ ha)
    · exact hyS (h ▸ ha)
  obtain ⟨P,hP,huvP⟩ := hmatch
  obtain ⟨A,B,huA,hvB,hAB,hpart,hcutG⟩ :=
    forced_zero_codegree_edge_partition_on_finset Hᶜ S u v hu hv P hP huvP hforced hcoS
  have hxu : x ∉ A ∪ B := by rw [hpart]; exact hxS
  have hyu : y ∉ A ∪ B := by rw [hpart]; exact hyS
  have hcut : ∀ a ∈ A, ∀ b ∈ B, (a ≠ u ∨ b ≠ v) → H.Adj a b := by
    intro a ha b hb h
    by_contra hn
    have hab : a ≠ b := by
      intro he
      exact (Finset.disjoint_left.mp hAB) ha (he ▸ hb)
    have habG : (Hᶜ).Adj a b := ⟨hab,hn⟩
    obtain ⟨hau,hbv⟩ := hcutG a ha b hb habG
    tauto
  have hxyA : ∀ a ∈ A ∪ B, H.Adj a x ∧ H.Adj a y := by
    intro a ha
    have haS : a ∈ S := hpart ▸ ha
    have hay : a ≠ y := Finset.ne_of_mem_erase haS
    have hxa : H.Adj x a := by
      have haN := Finset.mem_of_mem_erase haS
      simpa using haN
    have hax : a ≠ x := hxa.ne.symm
    exact ⟨hxa.symm, ((htwin a hax hay).mp hxa).symm⟩
  have hxC : x ∉ C := by simp [C]
  have hyC : y ∉ C := by simp [C, hxy]
  have hCS : Disjoint C (A ∪ B) := by
    rw [hpart]
    apply Finset.disjoint_left.mpr
    intro a haC haS
    have haG : (Hᶜ).Adj x a := by simpa [C] using haC
    have haH : H.Adj x a := by
      have := Finset.mem_of_mem_erase haS
      simpa using this
    exact haG.2 haH
  have habsum : A.card + B.card = S.card := by
    have hc := congrArg Finset.card hpart
    rw [Finset.card_union_of_disjoint hAB] at hc
    exact hc
  have hsize : A.card + B.card + 1 = d := by omega
  have hxyG := complement_adjacent_twins_have_equal_open_neighbors H x y hxy htwin
  have hfamily : ∀ z ∈ C, ∃ Q W : Finset (Fin (2*k+d+3)),
      x ∉ Q ∧ y ∉ Q ∧ W ⊆ A ∪ B ∧ W.Nonempty ∧ Q.Nonempty ∧ Q.card + W.card = d+1 ∧
      (∀ w ∈ W, H.Adj x w ∧ H.Adj y w) ∧
      (∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) ∧ (∀ q ∈ Q, H.Adj z q) ∧
      ∃ P : ((Hᶜ).induce {a | a ∈ W}).Subgraph, P.IsPerfectMatching := by
    intro z hzC
    have hxzG : (Hᶜ).Adj x z := by simpa [C] using hzC
    obtain ⟨R,hR,hxR,hzR,hPM,hf⟩ := hwitness z hxzG
    have hmaxG : ∀ a, (((Hᶜ)ᶜ).neighborFinset a).card ≤ d := by
      intro a
      have hN : (((Hᶜ)ᶜ).neighborFinset a) = H.neighborFinset a := by
        ext b
        simp
      rw [hN]
      exact hmax a
    obtain ⟨hyR,Q,W,hdis,hpartR,hxQ,hzQ,hxW,hzW,hyQ,hyW,hqmin,hwmin,hqe,hwe,hsum,hzQ,hxyW,hcross⟩ :=
      factorcritical_false_twin_forced_bridge_residual_shores Hᶜ k hcrit rfl x y z hxy.ne hxyG hxzG hmaxG R hR hxR hzR hPM hf
    have hwsub : W ⊆ A ∪ B := by
      rw [hpart]
      intro w hw
      have hwH : H.Adj x w := by simpa using (hxyW w hw).1
      have hwy : w ≠ y := fun h => hyW (h ▸ hw)
      exact Finset.mem_erase.mpr ⟨hwy, by simpa using hwH⟩
    have hwne : W.Nonempty := Finset.card_pos.mp (by omega)
    have hqne : Q.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨P',hP'⟩ := hPM
    have hxzP := perfect_matching_forced_edge_in_every_matching _ ⟨x,hxR⟩ ⟨z,hzR⟩ hf P' hP'
    have hcrossG : ∀ q ∈ Q, ∀ w ∈ W, ¬ (Hᶜ).Adj q w := by
      intro q hq w hw h
      have hab : H.Adj q w := by simpa using hcross q hq w hw
      exact h.2 hab
    have hWmatch := matched_residual_bridge_shore_has_perfect_matching Hᶜ R Q W x z hxR hzR P' hP' hxzP hpartR hxW hzW hcrossG
    refine ⟨Q,W,hxQ,hyQ,hwsub,hwne,hqne,hsum,?_,?_,?_,hWmatch⟩
    · intro w hw
      simpa using hxyW w hw
    · intro q hq w hw
      simpa using hcross q hq w hw
    · intro q hq
      simpa using hzQ q hq
  have hbound := factorcritical_bridge_family_endpoint_bound k d H hcrit x y u v hxy.ne huv.2 hcommon A B C hAB huA hvB hxu hyu hxC hyC hCS hsize hxyA hcut hmax hfamily
  have hCcard : C.card = 2*k+2 := by
    dsimp [C]
    change (Hᶜ).degree x = 2*k+2
    have hdeg : H.degree x = d := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hxdeg
    have hc := H.degree_compl (v := x)
    simp only [Fintype.card_fin] at hc
    rw [hdeg] at hc
    omega
  omega
