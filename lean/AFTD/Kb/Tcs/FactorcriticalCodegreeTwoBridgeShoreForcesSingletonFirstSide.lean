import AFTD.Prelude
import AFTD.Kb.Tcs.FactorcriticalFirstBridgeSecondShoreDoesNotCross
import AFTD.Kb.Tcs.FactorcriticalCrossingEvenShoreCoversOppositeFirstSide
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# factorcritical_codegree_two_bridge_shore_forces_singleton_first_side

Topic: graphs   Node: b7f7ea3a44bc

Provenance: helper lemma. OP-1957 crossing-cut reduction extending the earlier codegree-one case.

In the first-bridge configuration, a second bridge endpoint of complement codegree at most two forces one of the odd first shores to be a singleton.
-/

theorem factorcritical_codegree_two_bridge_shore_forces_singleton_first_side (k d : ℕ) (H : SimpleGraph (Fin (2*k+d+3))) [DecidableRel H.Adj] (hcrit : is_k_factor_critical Hᶜ (2*k)) (x y u v z : Fin (2*k+d+3)) (hxy : x ≠ y) (huv : ¬ H.Adj u v) (hcommon : ∀ a, H.Adj u a → H.Adj v a → a = x ∨ a = y) (A B Q W : Finset (Fin (2*k+d+3))) (hAB : Disjoint A B) (hxu : x ∉ A ∪ B) (hyu : y ∉ A ∪ B) (hqx : x ∉ Q) (hqy : y ∉ Q) (hu : u ∈ A) (hv : v ∈ B) (hcut : ∀ a ∈ A, ∀ b ∈ B, (a ≠ u ∨ b ≠ v) → H.Adj a b) (hwsub : W ⊆ A ∪ B) (hwne : W.Nonempty) (hqne : Q.Nonempty) (hAodd : Odd A.card) (hBodd : Odd B.card) (hevenA : Even (W ∩ A).card) (hevenB : Even (W ∩ B).card) (hsize : Q.card + W.card = d+1) (hxyW : ∀ w ∈ W, H.Adj x w ∧ H.Adj y w) (hxS : ∀ a ∈ A ∪ B, H.Adj x a) (hcross : ∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) (hqz : ∀ q ∈ Q, H.Adj z q) (hzco : ((Finset.univ : Finset (Fin (2*k+d+3))).filter (fun a => H.Adj x a ∧ H.Adj z a)).card ≤ 2) : A.card = 1 ∨ B.card = 1 := by
  classical
  let C : Finset (Fin (2*k+d+3)) := Finset.univ.filter (fun a => H.Adj x a ∧ H.Adj z a)
  have hQC : Q ∩ (A ∪ B) ⊆ C := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxS a (Finset.mem_inter.mp ha).2,
      hqz a (Finset.mem_inter.mp ha).1⟩
  have hQle : (Q ∩ (A ∪ B)).card ≤ 2 := by
    have h := Finset.card_le_card hQC
    dsimp [C] at h
    omega
  have hcut' : ∀ b ∈ B, ∀ a ∈ A, (b ≠ v ∨ a ≠ u) → H.Adj b a := by
    intro b hb a ha h
    apply (hcut a ha b hb ?_).symm
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hcoverA (h : (W ∩ B).Nonempty) : A ⊆ W ∪ Q := by
    apply factorcritical_crossing_even_shore_covers_opposite_first_side k d H hcrit x y v u hxy B A Q W hAB.symm
      (by simpa [Finset.union_comm] using hxu) (by simpa [Finset.union_comm] using hyu)
      hqx hqy hv hu hcut' (by simpa [Finset.union_comm] using hwsub) hevenB h hsize hxyW hcross
  have hcoverB (h : (W ∩ A).Nonempty) : B ⊆ W ∪ Q :=
    factorcritical_crossing_even_shore_covers_opposite_first_side k d H hcrit x y u v hxy A B Q W hAB hxu hyu hqx hqy hu hv hcut hwsub hevenA h hsize hxyW hcross
  have hn := factorcritical_first_bridge_second_shore_does_not_cross k d H hcrit x y u v hxy huv hcommon A B Q W hAB hxu hyu hqx hqy hu hv hcut hwsub hwne hqne hevenA hevenB hsize hxyW hcross
  rcases hn with hWA | hWB
  · left
    have hWBne : (W ∩ B).Nonempty := by
      obtain ⟨w,hw⟩ := hwne
      rcases Finset.mem_union.mp (hwsub hw) with hA | hB
      · exact ((Finset.disjoint_left.mp hWA) hw hA).elim
      · exact ⟨w,Finset.mem_inter.mpr ⟨hw,hB⟩⟩
    have hacover := hcoverA hWBne
    have hAsub : A ⊆ Q ∩ (A ∪ B) := by
      intro a ha
      have haW : a ∉ W := fun hw => (Finset.disjoint_left.mp hWA) hw ha
      have haQ : a ∈ Q := by
        rcases Finset.mem_union.mp (hacover ha) with h | h
        · exact (haW h).elim
        · exact h
      exact Finset.mem_inter.mpr ⟨haQ,Finset.mem_union_left B ha⟩
    have hc := Finset.card_le_card hAsub
    have hp : 0 < A.card := Finset.card_pos.mpr ⟨u,hu⟩
    rcases hAodd with ⟨a,ha⟩
    omega
  · right
    have hWAne : (W ∩ A).Nonempty := by
      obtain ⟨w,hw⟩ := hwne
      rcases Finset.mem_union.mp (hwsub hw) with hA | hB
      · exact ⟨w,Finset.mem_inter.mpr ⟨hw,hA⟩⟩
      · exact ((Finset.disjoint_left.mp hWB) hw hB).elim
    have hbcover := hcoverB hWAne
    have hBsub : B ⊆ Q ∩ (A ∪ B) := by
      intro b hb
      have hbW : b ∉ W := fun hw => (Finset.disjoint_left.mp hWB) hw hb
      have hbQ : b ∈ Q := by
        rcases Finset.mem_union.mp (hbcover hb) with h | h
        · exact (hbW h).elim
        · exact h
      exact Finset.mem_inter.mpr ⟨hbQ,Finset.mem_union_right A hb⟩
    have hc := Finset.card_le_card hBsub
    have hp : 0 < B.card := Finset.card_pos.mpr ⟨v,hv⟩
    rcases hBodd with ⟨b,hb⟩
    omega
