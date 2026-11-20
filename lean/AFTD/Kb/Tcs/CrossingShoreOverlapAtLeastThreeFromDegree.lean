import AFTD.Prelude

/-!
# crossing_shore_overlap_at_least_three_from_degree

Topic: graphs   Node: ec6de5d1486c

Provenance: helper lemma. Local-degree constraint in the OP-1957 crossing-cut route.

In a finite graph of maximum degree d, under the displayed cross-adjacency, twin-neighbor and crossing-cardinality assumptions, two intersecting W shores share at least three vertices.
-/

theorem crossing_shore_overlap_at_least_three_from_degree
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (d : ℕ) (W₁ W₂ Q₁ Q₂ : Finset V) (x y : V)
    (hWi : (W₁ ∩ W₂).Nonempty) (hxy : x ≠ y)
    (hxQ : x ∉ Q₁ ∪ Q₂) (hyQ : y ∉ Q₁ ∪ Q₂)
    (hsize₁ : W₁.card + Q₁.card = d + 1)
    (hsize₂ : W₂.card + Q₂.card = d + 1)
    (heq : (W₁ ∪ W₂).card + (Q₁ ∩ Q₂).card = d + 1)
    (hcross₁ : ∀ w ∈ W₁, ∀ q ∈ Q₁, H.Adj w q)
    (hcross₂ : ∀ w ∈ W₂, ∀ q ∈ Q₂, H.Adj w q)
    (htwins : ∀ w ∈ W₁ ∩ W₂, H.Adj w x ∧ H.Adj w y)
    (hdegree : ∀ w, (H.neighborFinset w).card ≤ d) :
    3 ≤ (W₁ ∩ W₂).card := by
  classical
  obtain ⟨w, hw⟩ := hWi
  have hw₁ := (Finset.mem_inter.mp hw).1
  have hw₂ := (Finset.mem_inter.mp hw).2
  have hxyQ : Disjoint ({x,y} : Finset V) (Q₁ ∪ Q₂) := by
    apply Finset.disjoint_left.mpr
    intro z hz hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxQ hq
    · exact hyQ hq
  have hsub : ({x,y} : Finset V) ∪ (Q₁ ∪ Q₂) ⊆ H.neighborFinset w := by
    intro z hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases Finset.mem_union.mp hz with hxy' | hq
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxy'
      rcases hxy' with rfl | rfl
      · exact (htwins w hw).1
      · exact (htwins w hw).2
    · rcases Finset.mem_union.mp hq with hq₁ | hq₂
      · exact hcross₁ w hw₁ z hq₁
      · exact hcross₂ w hw₂ z hq₂
  have hbudget := (Finset.card_le_card hsub).trans (hdegree w)
  rw [Finset.card_union_of_disjoint hxyQ, Finset.card_pair hxy] at hbudget
  have hW := Finset.card_union_add_card_inter W₁ W₂
  have hQ := Finset.card_union_add_card_inter Q₁ Q₂
  omega
