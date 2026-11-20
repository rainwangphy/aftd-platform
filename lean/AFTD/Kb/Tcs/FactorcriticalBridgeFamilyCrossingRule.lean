import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.FactorcriticalSeparatorLowerBound
import AFTD.Kb.Tcs.CrossingShoresForceTwoCommonOppositeVertices
import AFTD.Kb.Tcs.CrossingBridgeShoresForceCutEquality
import AFTD.Kb.Tcs.FactorcriticalCrossingShoreIntersectionEven

/-!
# factorcritical_bridge_family_crossing_rule

Topic: graphs   Node: cac611d1780f

Provenance: helper lemma. OP-1957 factor-critical bridge-family crossing-cut link; scratch Lean axiom audit completed.

In the displayed 2k-factor-critical graph, overlapping even bridge shores satisfy the crossing-cut equality and intersect evenly.
-/

theorem factorcritical_bridge_family_crossing_rule
    (k : ℕ) (H : SimpleGraph (Fin (2*k+11+3))) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical Hᶜ (2*k))
    (x y : Fin (2*k+11+3)) (hxy : x ≠ y)
    (S C : Finset (Fin (2*k+11+3))) (hS : S.card=10) (hSC : Disjoint S C)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : Fin (2*k+11+3) → Finset (Fin (2*k+11+3)))
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hW : ∀ z ∈ C, W z ⊆ S) (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=12)
    (hWeven : ∀ z ∈ C, Even (W z).card)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w) :
    ∀ z ∈ C, ∀ z' ∈ C, (W z ∩ W z').Nonempty →
      (W z ∪ W z').card + (Q z ∩ Q z').card = 12 ∧ Even (W z ∩ W z').card := by
  classical
  intro z hz z' hz' hWi
  by_cases hzz : z=z'
  · subst z'
    simp only [Finset.inter_self,Finset.union_self]
    constructor
    · have hs := hsize z hz
      omega
    · exact hWeven z hz
  · have hsep : ∀ C' A B : Finset (Fin (2*k+11+3)),
        A.Nonempty → B.Nonempty → Disjoint C' A → Disjoint C' B → Disjoint A B →
        C' ∪ A ∪ B = Finset.univ →
        (∀ a ∈ A, ∀ b ∈ B, ¬ Hᶜ.Adj a b) → 2*k ≤ C'.card :=
      factorcritical_separator_lower_bound k 11 Hᶜ hcrit
    have hxS : x ∉ S := by intro h; exact (hSxy x h).1.ne rfl
    have hyS : y ∉ S := by intro h; exact (hSxy y h).2.ne rfl
    have hxW : x ∉ W z ∪ W z' := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hxS (hW z hz h)
      · exact hxS (hW z' hz' h)
    have hyW : y ∉ W z ∪ W z' := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hyS (hW z hz h)
      · exact hyS (hW z' hz' h)
    have hxQ' : x ∉ Q z ∪ Q z' := by simp [hxQ z hz,hxQ z' hz']
    have hyQ' : y ∉ Q z ∪ Q z' := by simp [hyQ z hz,hyQ z' hz']
    have hzW : z ∉ W z ∪ W z' := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact (Finset.disjoint_left.mp hSC) (hW z hz h) hz
      · exact (Finset.disjoint_left.mp hSC) (hW z' hz' h) hz
    have hz'W : z' ∉ W z ∪ W z' := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact (Finset.disjoint_left.mp hSC) (hW z hz h) hz'
      · exact (Finset.disjoint_left.mp hSC) (hW z' hz' h) hz'
    have hzQi : z ∉ Q z ∩ Q z' := by
      intro h
      exact (hzQ z hz z (Finset.mem_inter.mp h).1).ne rfl
    have hz'Qi : z' ∉ Q z ∩ Q z' := by
      intro h
      exact (hzQ z' hz' z' (Finset.mem_inter.mp h).2).ne rfl
    have hdisj₁ : Disjoint (W z ∩ W z') (Q z ∪ Q z') := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact (Finset.disjoint_left.mp (hdis z hz)) hb (Finset.mem_inter.mp ha).1
      · exact (Finset.disjoint_left.mp (hdis z' hz')) hb (Finset.mem_inter.mp ha).2
    have hdisj₂ : Disjoint (Q z ∩ Q z') (W z ∪ W z') := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact (Finset.disjoint_left.mp (hdis z hz)) (Finset.mem_inter.mp ha).1 hb
      · exact (Finset.disjoint_left.mp (hdis z' hz')) (Finset.mem_inter.mp ha).2 hb
    have hcross₁ : ∀ w ∈ W z, ∀ q ∈ Q z, ¬ Hᶜ.Adj w q := by
      intro w hw q hq hadj
      exact hadj.2 (hcross z hz q hq w hw).symm
    have hcross₂ : ∀ w ∈ W z', ∀ q ∈ Q z', ¬ Hᶜ.Adj w q := by
      intro w hw q hq hadj
      exact hadj.2 (hcross z' hz' q hq w hw).symm
    have htwins : ∀ w ∈ W z ∪ W z', ¬ Hᶜ.Adj w x ∧ ¬ Hᶜ.Adj w y := by
      intro w hw
      have hwS : w ∈ S := by
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hW z hz hw
        · exact hW z' hz' hw
      exact ⟨fun ha => ha.2 (hSxy w hwS).1, fun ha => ha.2 (hSxy w hwS).2⟩
    have hend : ∀ q ∈ Q z ∩ Q z', ¬ Hᶜ.Adj q z ∧ ¬ Hᶜ.Adj q z' := by
      intro q hq
      exact ⟨fun ha => ha.2 (hzQ z hz q (Finset.mem_inter.mp hq).1).symm,
        fun ha => ha.2 (hzQ z' hz' q (Finset.mem_inter.mp hq).2).symm⟩
    have hWbound : (W z ∪ W z').card+1 ≤ 11 := by
      have hs : W z ∪ W z' ⊆ S := Finset.union_subset (hW z hz) (hW z' hz')
      have hc := Finset.card_le_card hs
      omega
    have hQi2 := crossing_shores_force_two_common_opposite_vertices k 11 Hᶜ (W z) (W z') (Q z) (Q z') x y
      hsep hWi (by have hs := hsize z hz; omega) (by have hs := hsize z' hz'; omega)
      hWbound hxy hxW hyW hxQ' hyQ' hdisj₁ hcross₁ hcross₂ htwins
    have hQi : (Q z ∩ Q z').Nonempty := Finset.card_pos.mp (by omega)
    have hcut := crossing_bridge_shores_force_cut_equality k 11 Hᶜ (W z) (W z') (Q z) (Q z') x y z z'
      hsep hWi hQi (by have hs := hsize z hz; omega) (by have hs := hsize z' hz'; omega)
      hxy hzz hxW hyW hxQ' hyQ' hzW hz'W hzQi hz'Qi hdisj₁ hdisj₂ hcross₁ hcross₂ htwins hend
    have hQeven : Even (Q z).card := by
      obtain ⟨m,hm⟩ := hWeven z hz
      have hs := hsize z hz
      refine ⟨6-m,?_⟩
      omega
    have heven := factorcritical_crossing_shore_intersection_even Hᶜ k 11 hcrit (W z) (W z') (Q z) (Q z') z z'
      (by have hs := hsize z hz; omega) (by have hs := hsize z' hz'; omega)
      (hWeven z hz) (hWeven z' hz') hQeven (by have := hcut.1; omega)
      (by simpa only [Finset.union_assoc] using hcut.2.2) hdisj₂ hzQi hz'Qi hcross₁ hcross₂ hend
    exact ⟨by have := hcut.1; omega,heven⟩
