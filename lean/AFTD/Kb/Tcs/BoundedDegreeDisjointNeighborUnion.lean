import AFTD.Prelude

/-!
# bounded_degree_disjoint_neighbor_union

Topic: graphs   Node: bf1ecfd794a2

Provenance: helper lemma. OP-1957 uniform saturated-first-bridge counting reduction.

A bounded-degree vertex with two distinguished neighbors and two disjoint sets of further neighbors has their total cardinality bounded by its degree.
-/

theorem bounded_degree_disjoint_neighbor_union {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (p x y : V) (K C : Finset V)
    (hxy : x ≠ y) (hxK : x ∉ K) (hyK : y ∉ K)
    (hxC : x ∉ C) (hyC : y ∉ C) (hdis : Disjoint K C)
    (hpx : H.Adj p x) (hpy : H.Adj p y)
    (hpK : ∀ a ∈ K, H.Adj p a) (hpC : ∀ a ∈ C, H.Adj p a)
    (d : ℕ) (hmax : (H.neighborFinset p).card ≤ d) : K.card + C.card + 2 ≤ d := by
  classical
  let T := insert x (insert y K)
  have hxT : x ∉ insert y K := by simp [hxy, hxK]
  have hTcard : T.card = K.card + 2 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem hxT, Finset.card_insert_of_notMem hyK]
  have hTC : Disjoint T C := by
    apply Finset.disjoint_left.mpr
    intro a ha hc
    simp only [T, Finset.mem_insert] at ha
    rcases ha with rfl | rfl | ha
    · exact hxC hc
    · exact hyC hc
    · exact (Finset.disjoint_left.mp hdis) ha hc
  have hsub : T ∪ C ⊆ H.neighborFinset p := by
    intro a ha
    rw [H.mem_neighborFinset]
    rcases Finset.mem_union.mp ha with ha | ha
    · simp only [T, Finset.mem_insert] at ha
      rcases ha with rfl | rfl | ha
      · exact hpx
      · exact hpy
      · exact hpK a ha
    · exact hpC a ha
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hTC, hTcard] at hle
  omega
