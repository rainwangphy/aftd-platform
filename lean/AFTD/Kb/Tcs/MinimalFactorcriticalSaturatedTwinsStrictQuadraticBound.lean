import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual
import AFTD.Kb.Tcs.ComplementAdjacentTwinsHaveEqualOpenNeighbors
import AFTD.Kb.Tcs.FactorcriticalFalseTwinForcedBridgeResidualShores
import AFTD.Kb.Tcs.SaturatedTwinBridgeFamilyStrictQuadraticBound
import AFTD.Kb.Tcs.IsKExtendable

/-!
# minimal_factorcritical_saturated_twins_strict_quadratic_bound

Topic: graphs   Node: 2a06a51287b9

Provenance: helper lemma. OP-1957 simultaneous saturated-twin bridge family, without the first zero-codegree witness.

A minimally k-extendible 2k-factor-critical graph with the displayed saturated complement twins satisfies 4(2k+2)<(d−1)(d−2).
-/

theorem minimal_factorcritical_saturated_twins_strict_quadratic_bound
    (k d : ℕ) (H : SimpleGraph (Fin (2*k+d+3))) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical Hᶜ (2*k)) (hmin : is_minimally_k_extendable Hᶜ k)
    (x y : Fin (2*k+d+3)) (hxy : H.Adj x y)
    (hxdeg : (H.neighborFinset x).card = d) (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (htwin : ∀ a, a ≠ x → a ≠ y → (H.Adj x a ↔ H.Adj y a)) :
    4*(2*k+2) < (d-1)*(d-2) := by
  classical
  let S := (H.neighborFinset x).erase y
  let C := (Hᶜ).neighborFinset x
  have hxS : x ∉ S := by simp [S]
  have hyS : y ∉ S := by simp [S]
  have hxC : x ∉ C := by simp [C]
  have hyC : y ∉ C := by simp [C,hxy]
  have hSC : Disjoint S C := by
    apply Finset.disjoint_left.mpr
    intro a haS haC
    have haG : (Hᶜ).Adj x a := by simpa [C] using haC
    have haH : H.Adj x a := by
      have := Finset.mem_of_mem_erase haS
      simpa using this
    exact haG.2 haH
  have hyN : y ∈ H.neighborFinset x := by simpa using hxy
  have hSsize : S.card+1=d := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hyN,hxdeg]
    have hdpos : 0 < d := by
      rw [← hxdeg]
      exact Finset.card_pos.mpr ⟨y,hyN⟩
    omega
  have hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y := by
    intro a haS
    have hay : a ≠ y := Finset.ne_of_mem_erase haS
    have hxa : H.Adj x a := by
      have haN := Finset.mem_of_mem_erase haS
      simpa using haN
    have hax : a ≠ x := hxa.ne.symm
    exact ⟨hxa.symm, ((htwin a hax hay).mp hxa).symm⟩
  have hxyG := complement_adjacent_twins_have_equal_open_neighbors H x y hxy htwin
  have hmaxG : ∀ a, (((Hᶜ)ᶜ).neighborFinset a).card ≤ d := by
    intro a
    have hN : (((Hᶜ)ᶜ).neighborFinset a) = H.neighborFinset a := by ext b; simp
    rw [hN]
    exact hmax a
  have hfamily : ∀ z ∈ C, ∃ Q W : Finset (Fin (2*k+d+3)),
      Disjoint Q W ∧ Q ⊆ S ∪ C ∧ W ⊆ S ∧ x ∉ Q ∧ y ∉ Q ∧
      Q.card+W.card=d+1 ∧ (∀ q ∈ Q, H.Adj z q) ∧
      (∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) ∧ 2 ≤ W.card ∧ Even Q.card ∧ Even W.card := by
    intro z hzC
    have hxzG : (Hᶜ).Adj x z := by simpa [C] using hzC
    have he : s(x,z) ∈ (Hᶜ).edgeSet := by simpa using hxzG
    have hessential := hmin.2 s(x,z) he
    obtain ⟨R,hR,hxR,hzR,hPM,hf⟩ := k_extendable_essential_edge_has_forced_matching_residual
      (2*k+d+3) k Hᶜ x z hxzG hmin.1 hessential
    have hR' : R.card=d+3 := by omega
    obtain ⟨hyR,Q,W,hdis,hpartR,hxQ,hzQ,hxW,hzW,hyQ,hyW,hqmin,hwmin,hqe,hwe,hsum,hzQ,hxyW,hcross⟩ :=
      factorcritical_false_twin_forced_bridge_residual_shores Hᶜ k hcrit rfl x y z hxy.ne hxyG hxzG hmaxG R hR' hxR hzR hPM hf
    have hQsub : Q ⊆ S ∪ C := by
      intro q hq
      have hqx : q ≠ x := fun h => hxQ (h ▸ hq)
      have hqy : q ≠ y := fun h => hyQ (h ▸ hq)
      by_cases h : H.Adj x q
      · apply Finset.mem_union_left
        exact Finset.mem_erase.mpr ⟨hqy, by simpa using h⟩
      · apply Finset.mem_union_right
        have hG : (Hᶜ).Adj x q := ⟨hqx.symm,h⟩
        simpa [C] using hG
    have hWsub : W ⊆ S := by
      intro w hw
      have hwH : H.Adj x w := by simpa using (hxyW w hw).1
      have hwy : w ≠ y := fun h => hyW (h ▸ hw)
      exact Finset.mem_erase.mpr ⟨hwy, by simpa using hwH⟩
    refine ⟨Q,W,hdis,hQsub,hWsub,hxQ,hyQ,hsum,?_,?_,hwmin,hqe,hwe⟩
    · intro q hq
      simpa using hzQ q hq
    · intro q hq w hw
      simpa using hcross q hq w hw
  have hfull : ∀ z, ∃ Q W : Finset (Fin (2*k+d+3)), z ∈ C →
      Disjoint Q W ∧ Q ⊆ S ∪ C ∧ W ⊆ S ∧ x ∉ Q ∧ y ∉ Q ∧
      Q.card+W.card=d+1 ∧ (∀ q ∈ Q, H.Adj z q) ∧
      (∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) ∧ 2 ≤ W.card ∧ Even Q.card ∧ Even W.card := by
    intro z
    by_cases hz : z ∈ C
    · obtain ⟨Q,W,h⟩ := hfamily z hz
      exact ⟨Q,W,fun _ => h⟩
    · exact ⟨∅,∅,fun h => (hz h).elim⟩
  choose Q W hp using hfull
  have hCcard : C.card = 2*k+2 := by
    dsimp [C]
    change (Hᶜ).degree x = 2*k+2
    have hdeg : H.degree x = d := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hxdeg
    have hc := H.degree_compl (v := x)
    simp only [Fintype.card_fin] at hc
    rw [hdeg] at hc
    omega
  have hCne : C.Nonempty := Finset.card_pos.mp (by rw [hCcard]; omega)
  have hb := saturated_twin_bridge_family_strict_quadratic_bound H x y hxy.ne S C d hCne hSC hxC hyC hSsize hmax hSxy Q W
    (by intro z hz; exact (hp z hz).1)
    (by intro z hz; exact (hp z hz).2.1)
    (by intro z hz; exact (hp z hz).2.2.1)
    (by intro z hz; exact (hp z hz).2.2.2.1)
    (by intro z hz; exact (hp z hz).2.2.2.2.1)
    (by intro z hz; exact (hp z hz).2.2.2.2.2.1)
    (by intro z hz; exact (hp z hz).2.2.2.2.2.2.1)
    (by intro z hz; exact (hp z hz).2.2.2.2.2.2.2.1)
    (by intro z hz; exact (hp z hz).2.2.2.2.2.2.2.2.1)
    (by intro z hz; exact (hp z hz).2.2.2.2.2.2.2.2.2.1)
    (by intro z hz; exact (hp z hz).2.2.2.2.2.2.2.2.2.2)
  rwa [hCcard] at hb
