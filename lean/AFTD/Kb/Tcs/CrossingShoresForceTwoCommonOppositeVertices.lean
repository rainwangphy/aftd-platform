import AFTD.Prelude
import AFTD.Kb.Tcs.TwoKConnectedAnticompleteSetsCardinalityBound

/-!
# crossing_shores_force_two_common_opposite_vertices

Topic: graphs   Node: 174859206e9e

Provenance: helper lemma. Crossing-cut bridge-to-set reduction in the OP-1957 campaign.

Under the displayed connectivity, cross-shore anticompleteness, twin and cardinality assumptions, if the W shores intersect and their union has size at most d−1, the two opposite Q shores share at least two vertices.
-/

theorem crossing_shores_force_two_common_opposite_vertices
    (k d : ℕ) (G : SimpleGraph (Fin (2 * k + d + 3)))
    (W₁ W₂ Q₁ Q₂ : Finset (Fin (2 * k + d + 3)))
    (x y : Fin (2 * k + d + 3))
    (hsep : ∀ C A B : Finset (Fin (2 * k + d + 3)),
      A.Nonempty → B.Nonempty → Disjoint C A → Disjoint C B → Disjoint A B →
      C ∪ A ∪ B = Finset.univ →
      (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) → 2 * k ≤ C.card)
    (hWi : (W₁ ∩ W₂).Nonempty)
    (hsize₁ : W₁.card + Q₁.card = d + 1)
    (hsize₂ : W₂.card + Q₂.card = d + 1)
    (hWbound : (W₁ ∪ W₂).card + 1 ≤ d)
    (hxy : x ≠ y)
    (hxW : x ∉ W₁ ∪ W₂) (hyW : y ∉ W₁ ∪ W₂)
    (hxQ : x ∉ Q₁ ∪ Q₂) (hyQ : y ∉ Q₁ ∪ Q₂)
    (hdisj : Disjoint (W₁ ∩ W₂) (Q₁ ∪ Q₂))
    (hcross₁ : ∀ w ∈ W₁, ∀ q ∈ Q₁, ¬ G.Adj w q)
    (hcross₂ : ∀ w ∈ W₂, ∀ q ∈ Q₂, ¬ G.Adj w q)
    (htwins : ∀ w ∈ W₁ ∪ W₂, ¬ G.Adj w x ∧ ¬ G.Adj w y) :
    2 ≤ (Q₁ ∩ Q₂).card := by
  classical
  let I := W₁ ∩ W₂
  let J := Q₁ ∩ Q₂
  let U := W₁ ∪ W₂
  let V := Q₁ ∪ Q₂
  have hIU : I ⊆ U := by
    intro w hw
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hw).1)
  have hIxy : Disjoint I ({x,y} : Finset _) := by
    apply Finset.disjoint_left.mpr
    intro w hw hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hxW (hIU hw)
    · exact hyW (hIU hw)
  have hVxy : Disjoint V ({x,y} : Finset _) := by
    apply Finset.disjoint_left.mpr
    intro q hq hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hxQ hq
    · exact hyQ hq
  have hIleft : Disjoint I (V ∪ {x,y}) :=
    Finset.disjoint_union_right.mpr ⟨hdisj, hIxy⟩
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
  have hB : (V ∪ {x,y}).Nonempty := by
    exact ⟨x, Finset.mem_union.mpr (Or.inr (by simp))⟩
  have hbd := two_k_connected_anticomplete_sets_cardinality_bound k d G I (V ∪ {x,y})
    hsep hWi hB hIleft hcrossI
  have hBcard : (V ∪ {x,y}).card = V.card + 2 := by
    rw [Finset.card_union_of_disjoint hVxy, Finset.card_pair hxy]
  rw [hBcard] at hbd
  have hWcard : U.card + I.card = W₁.card + W₂.card := Finset.card_union_add_card_inter _ _
  have hQcard : V.card + J.card = Q₁.card + Q₂.card := Finset.card_union_add_card_inter _ _
  dsimp [I, J, U, V] at hbd hWcard hQcard
  change 2 ≤ (Q₁ ∩ Q₂).card
  omega
