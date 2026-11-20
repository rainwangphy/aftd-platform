import AFTD.Prelude
import AFTD.Kb.Tcs.D11NestedFirstFourShoreImpossible
import AFTD.Kb.Tcs.BridgeFamilyHasNoFullFirstNeighborhoodShore
import AFTD.Kb.Tcs.D11FourShoreHasAtMostTwoInternalOppositeVertices
import AFTD.Kb.Tcs.FourShoreForcesOtherOppositeAvoidsShore
import AFTD.Kb.Tcs.FourShoreEvenCrossingIsContained

/-!
# d11_factorcritical_crossing_large_bridge_family_has_no_four_shore

Topic: graphs   Node: 5722012d97fc

Provenance: helper lemma. OP-1957 d=11 saturated-twin family; scratch Lean axiom audit completed.

A factor-critical crossing bridge family with at least twenty external endpoints has no four-vertex shore.
-/

theorem d11_factorcritical_crossing_large_bridge_family_has_no_four_shore
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S C : Finset V) (hC : 20 ≤ C.card) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hS : S.card = 10)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=12)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, 4 ≤ (W z).card) (hWeven : ∀ z ∈ C, Even (W z).card)
    (hcutrule : ∀ z ∈ C, ∀ z' ∈ C, (W z ∩ W z').Nonempty →
      (W z ∪ W z').card + (Q z ∩ Q z').card = 12 ∧ Even (W z ∩ W z').card) :
    ∀ z ∈ C, (W z).card ≠ 4 := by
  classical
  intro z₀ hz₀ hw4
  let A := W z₀
  let B := Q z₀
  have hA : A ⊆ S := hW z₀ hz₀
  have hAcard : A.card=4 := hw4
  have hB : B ⊆ S ∪ C := hQ z₀ hz₀
  have hBcard : B.card=8 := by have hs := hsize z₀ hz₀; dsimp [A,B] at *; omega
  have hxB : x ∉ B := hxQ z₀ hz₀
  have hyB : y ∉ B := hyQ z₀ hz₀
  have hfamily : ∀ z ∈ C, ∃ Q' W' : Finset V, Disjoint Q' W' ∧ Q' ⊆ S ∪ C ∧ W' ⊆ S ∧
      Q'.card+W'.card=11+1 ∧ (∀ q ∈ Q', H.Adj z q) ∧
      (∀ q ∈ Q', ∀ w ∈ W', H.Adj q w) := by
    intro z hz
    exact ⟨Q z,W z,hdis z hz,hQ z hz,hW z hz,by simpa using hsize z hz,hzQ z hz,hcross z hz⟩
  have hW8 : ∀ z ∈ C, (W z).card ≤ 8 := by
    intro z hz
    have hne := bridge_family_has_no_full_first_neighborhood_shore H S C 11 hSC (by omega) hmax hfamily
      z hz (Q z) (W z) (hdis z hz) (hQ z hz) (hW z hz) (by simpa using hsize z hz)
      (hzQ z hz) (hcross z hz)
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hW z hz,hne⟩)
    obtain ⟨m,hm⟩ := hWeven z hz
    omega
  have hQ4 : ∀ z ∈ C, 4 ≤ (Q z).card := by
    intro z hz
    have hw := hW8 z hz
    have hs := hsize z hz
    omega
  have hprod : ∀ z ∈ C, 32 ≤ (W z).card*(Q z).card := by
    intro z hz
    have hw4 := hWmin z hz
    have hw8 := hW8 z hz
    have hs := hsize z hz
    obtain ⟨m,hm⟩ := hWeven z hz
    have hwcase : (W z).card=4 ∨ (W z).card=6 ∨ (W z).card=8 := by omega
    rcases hwcase with hw | hw | hw <;> rw [hw] <;> omega
  have hBS : (B ∩ S).card ≤ 2 := by
    have hb := d11_four_shore_has_at_most_two_internal_opposite_vertices H x y hxy S C
      (by omega) hSC hxC hyC (by omega) hmax hSxy Q W hdis hQ hW hxQ hyQ hsize hzQ hcross hWmin hprod
      z₀ hz₀ hw4
    exact hb
  have hE : 6 ≤ (B ∩ C).card := by
    have hd : Disjoint (B ∩ S) (B ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have heq : (B ∩ S) ∪ (B ∩ C) = B := by
      ext a
      simp only [Finset.mem_union,Finset.mem_inter]
      constructor
      · rintro (⟨ha,_⟩ | ⟨ha,_⟩) <;> exact ha
      · intro ha
        rcases Finset.mem_union.mp (hB ha) with haS | haC
        · exact Or.inl ⟨ha,haS⟩
        · exact Or.inr ⟨ha,haC⟩
    have hc := congrArg Finset.card heq
    rw [Finset.card_union_of_disjoint hd] at hc
    omega
  have havoid : ∀ z ∈ C, Disjoint A (Q z) := by
    intro z hz
    exact four_shore_forces_other_opposite_avoids_shore H x y hxy S A B (Q z) (W z)
      hA (hW z hz) hBcard (hWmin z hz) hBS hxB hyB hmax hSxy
      (by intro b hb a ha; exact hcross z₀ hz₀ b hb a ha)
      (hcross z hz)
  have hnest : ∀ z ∈ C, (A ∩ W z).Nonempty → A ⊆ W z ∧ Q z ⊆ B := by
    intro z hz hAW
    have hc := hcutrule z₀ hz₀ z hz hAW
    obtain ⟨heq,heven⟩ := hc
    have hAWsub := four_shore_even_crossing_is_contained H x y hxy S A B (W z) (Q z)
      hA hAcard hBcard (by have hs := hsize z hz; omega) heq hAW heven hxB hyB (hxQ z hz) (hyQ z hz)
      hmax hSxy
      (by intro b hb a ha; exact hcross z₀ hz₀ b hb a ha)
      (hcross z hz)
    refine ⟨hAWsub,?_⟩
    have huni : A ∪ W z = W z := Finset.union_eq_right.mpr hAWsub
    rw [huni] at heq
    change (W z).card + (B ∩ Q z).card = 12 at heq
    have hcard : (B ∩ Q z).card = (Q z).card := by have hs := hsize z hz; omega
    have hset : B ∩ Q z = Q z := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    intro q hq
    exact (Finset.mem_inter.mp (hset.symm ▸ hq)).1
  exact d11_nested_first_four_shore_impossible H x y z₀ hxy S C A B Q W
    hSC hxC hyC hS hA hAcard hB hBcard hBS hE hz₀ rfl rfl hxB hyB hmax hSxy hQ hW hdis hsize hQ4 hWmin
    hWeven (by intro z hz; exact hW8 z (Finset.mem_inter.mp hz).2) havoid hzQ hcross hnest
