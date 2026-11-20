import AFTD.Prelude
import AFTD.Kb.Tcs.TwoKConnectedAnticompleteSetsCardinalityBound

/-!
# crossing_bridge_shores_force_cut_equality

Topic: graphs   Node: 4530ed842096

Provenance: helper lemma. Crossing minimum-cut equality in the OP-1957 equality-case two-critical-bridge route.

In a graph on 2k+d+3 vertices with no separator smaller than 2k, suppose two bridge-shore pairs Wᵢ,Qᵢ have |Wᵢ|+|Qᵢ|=d+1, both W and Q intersections are nonempty, the W intersection is disjoint from the Q union and vice versa, and the stated twin, endpoint, and cross-shore nonadjacencies hold. Then |W₁ ∪ W₂|+|Q₁ ∩ Q₂|=d+1, and both crossing separators have exactly 2k vertices.
-/

theorem crossing_bridge_shores_force_cut_equality
    (k d : ℕ) (G : SimpleGraph (Fin (2 * k + d + 3)))
    (W₁ W₂ Q₁ Q₂ : Finset (Fin (2 * k + d + 3)))
    (x y z₁ z₂ : Fin (2 * k + d + 3))
    (hsep : ∀ C A B : Finset (Fin (2 * k + d + 3)),
      A.Nonempty → B.Nonempty → Disjoint C A → Disjoint C B → Disjoint A B →
      C ∪ A ∪ B = Finset.univ →
      (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) → 2 * k ≤ C.card)
    (hWi : (W₁ ∩ W₂).Nonempty) (hQi : (Q₁ ∩ Q₂).Nonempty)
    (hsize₁ : W₁.card + Q₁.card = d + 1)
    (hsize₂ : W₂.card + Q₂.card = d + 1)
    (hxy : x ≠ y) (hzz : z₁ ≠ z₂)
    (hxW : x ∉ W₁ ∪ W₂) (hyW : y ∉ W₁ ∪ W₂)
    (hxQ : x ∉ Q₁ ∪ Q₂) (hyQ : y ∉ Q₁ ∪ Q₂)
    (hz₁W : z₁ ∉ W₁ ∪ W₂) (hz₂W : z₂ ∉ W₁ ∪ W₂)
    (hz₁Q : z₁ ∉ Q₁ ∩ Q₂) (hz₂Q : z₂ ∉ Q₁ ∩ Q₂)
    (hdisj₁ : Disjoint (W₁ ∩ W₂) (Q₁ ∪ Q₂))
    (hdisj₂ : Disjoint (Q₁ ∩ Q₂) (W₁ ∪ W₂))
    (hcross₁ : ∀ w ∈ W₁, ∀ q ∈ Q₁, ¬ G.Adj w q)
    (hcross₂ : ∀ w ∈ W₂, ∀ q ∈ Q₂, ¬ G.Adj w q)
    (htwins : ∀ w ∈ W₁ ∪ W₂, ¬ G.Adj w x ∧ ¬ G.Adj w y)
    (hend : ∀ q ∈ Q₁ ∩ Q₂, ¬ G.Adj q z₁ ∧ ¬ G.Adj q z₂) :
    (W₁ ∪ W₂).card + (Q₁ ∩ Q₂).card = d + 1 ∧
    (Finset.univ \ ((W₁ ∩ W₂) ∪ (Q₁ ∪ Q₂) ∪ {x, y})).card = 2 * k ∧
    (Finset.univ \ ((Q₁ ∩ Q₂) ∪ (W₁ ∪ W₂) ∪ {z₁, z₂})).card = 2 * k := by
  classical
  let I := W₁ ∩ W₂
  let J := Q₁ ∩ Q₂
  let U := W₁ ∪ W₂
  let V := Q₁ ∪ Q₂
  have hIU : I ⊆ U := by
    intro x hx
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hx).1)
  have hJV : J ⊆ V := by
    intro x hx
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hx).1)
  have hIxy : Disjoint I ({x,y} : Finset _) := by
    apply Finset.disjoint_left.mpr
    intro w hw hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hxW (hIU hw)
    · exact hyW (hIU hw)
  have hJzz : Disjoint J ({z₁,z₂} : Finset _) := by
    apply Finset.disjoint_left.mpr
    intro q hq hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hz₁Q hq
    · exact hz₂Q hq
  have hVxy : Disjoint V ({x,y} : Finset _) := by
    apply Finset.disjoint_left.mpr
    intro q hq hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hxQ hq
    · exact hyQ hq
  have hUzz : Disjoint U ({z₁,z₂} : Finset _) := by
    apply Finset.disjoint_left.mpr
    intro w hw hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hz₁W hw
    · exact hz₂W hw
  have hIleft : Disjoint I (V ∪ {x,y}) :=
    Finset.disjoint_union_right.mpr ⟨hdisj₁, hIxy⟩
  have hJleft : Disjoint J (U ∪ {z₁,z₂}) :=
    Finset.disjoint_union_right.mpr ⟨hdisj₂, hJzz⟩
  have hcrossI : ∀ w ∈ I, ∀ q ∈ V ∪ {x,y}, ¬ G.Adj w q := by
    intro w hw q hq
    have hwI := Finset.mem_inter.mp hw
    rcases Finset.mem_union.mp hq with hqV | hqxy
    · rcases Finset.mem_union.mp hqV with hq1 | hq2
      · exact hcross₁ w hwI.1 q hq1
      · exact hcross₂ w hwI.2 q hq2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hqxy
      rcases hqxy with rfl | rfl
      · exact (htwins w (hIU hw)).1
      · exact (htwins w (hIU hw)).2
  have hcrossJ : ∀ q ∈ J, ∀ w ∈ U ∪ {z₁,z₂}, ¬ G.Adj q w := by
    intro q hq w hw
    have hqJ := Finset.mem_inter.mp hq
    rcases Finset.mem_union.mp hw with hwU | hwzz
    · rcases Finset.mem_union.mp hwU with hw1 | hw2
      · exact fun h => hcross₁ w hw1 q hqJ.1 h.symm
      · exact fun h => hcross₂ w hw2 q hqJ.2 h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hwzz
      rcases hwzz with rfl | rfl
      · exact (hend q hq).1
      · exact (hend q hq).2
  have hB1 : (V ∪ {x,y}).Nonempty := by
    exact ⟨x, Finset.mem_union.mpr (Or.inr (by simp))⟩
  have hB2 : (U ∪ {z₁,z₂}).Nonempty := by
    exact ⟨z₁, Finset.mem_union.mpr (Or.inr (by simp))⟩
  have hbd1 := two_k_connected_anticomplete_sets_cardinality_bound k d G I (V ∪ {x,y})
    hsep hWi hB1 hIleft hcrossI
  have hbd2 := two_k_connected_anticomplete_sets_cardinality_bound k d G J (U ∪ {z₁,z₂})
    hsep hQi hB2 hJleft hcrossJ
  have hB1card : (V ∪ {x,y}).card = V.card + 2 := by
    rw [Finset.card_union_of_disjoint hVxy, Finset.card_pair hxy]
  have hB2card : (U ∪ {z₁,z₂}).card = U.card + 2 := by
    rw [Finset.card_union_of_disjoint hUzz, Finset.card_pair hzz]
  rw [hB1card] at hbd1
  rw [hB2card] at hbd2
  have hWcard : U.card + I.card = W₁.card + W₂.card := Finset.card_union_add_card_inter _ _
  have hQcard : V.card + J.card = Q₁.card + Q₂.card := Finset.card_union_add_card_inter _ _
  have heq : U.card + J.card = d + 1 := by omega
  have htotal1 : (I ∪ (V ∪ {x,y})).card = d + 3 := by
    rw [Finset.card_union_of_disjoint hIleft, hB1card]
    omega
  have htotal2 : (J ∪ (U ∪ {z₁,z₂})).card = d + 3 := by
    rw [Finset.card_union_of_disjoint hJleft, hB2card]
    omega
  have hc1 : ((Finset.univ : Finset (Fin (2 * k + d + 3))) \ (I ∪ (V ∪ {x,y}))).card = 2 * k := by
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (I ∪ (V ∪ {x,y})))
    simp only [Finset.card_univ, Fintype.card_fin, htotal1] at hc
    omega
  have hc2 : ((Finset.univ : Finset (Fin (2 * k + d + 3))) \ (J ∪ (U ∪ {z₁,z₂}))).card = 2 * k := by
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (J ∪ (U ∪ {z₁,z₂})))
    simp only [Finset.card_univ, Fintype.card_fin, htotal2] at hc
    omega
  refine ⟨heq, ?_, ?_⟩
  · simpa only [I, V, Finset.union_assoc] using hc1
  · simpa only [J, U, Finset.union_assoc] using hc2
