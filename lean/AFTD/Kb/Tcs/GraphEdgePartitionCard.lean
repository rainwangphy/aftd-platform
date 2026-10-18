import AFTD.Prelude
import AFTD.Kb.Tcs.GraphEdgeVertexPartition

/-!
# graph_edge_partition_card

Topic: graphs   Node: c074987fc579

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

With the four-part partition of V induced by an edge xy: deg x = |A| + |C| + 1, deg y = |B| + |C| + 1, and |V| = 2 + |A| + |B| + |C| + |P|.
-/

/-- Degree and vertex-count identities for the edge partition. -/
theorem graph_edge_partition_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (hxy : G.Adj x y)
    (A B C P : Finset V)
    (hAmem : ∀ v, v ∈ A ↔ (G.Adj x v ∧ ¬ G.Adj y v ∧ v ≠ y))
    (hBmem : ∀ v, v ∈ B ↔ (G.Adj y v ∧ ¬ G.Adj x v ∧ v ≠ x))
    (hCmem : ∀ v, v ∈ C ↔ (G.Adj x v ∧ G.Adj y v))
    (hPmem : ∀ v, v ∈ P ↔ (¬ G.Adj x v ∧ ¬ G.Adj y v))
    (hcover : (Finset.univ : Finset V) = {x} ∪ {y} ∪ A ∪ B ∪ C ∪ P) :
    G.degree x = A.card + C.card + 1 ∧
      G.degree y = B.card + C.card + 1 ∧
      Fintype.card V = 2 + A.card + B.card + C.card + P.card := by
  have hxyne : x ≠ y := hxy.ne
  have hxA : x ∉ A := fun h => G.irrefl ((hAmem x).mp h).1
  have hyA : y ∉ A := fun h => ((hAmem y).mp h).2.2 rfl
  have hxB : x ∉ B := fun h => ((hBmem x).mp h).2.2 rfl
  have hyB : y ∉ B := fun h => G.irrefl ((hBmem y).mp h).1
  have hxC : x ∉ C := fun h => G.irrefl ((hCmem x).mp h).1
  have hyC : y ∉ C := fun h => G.irrefl ((hCmem y).mp h).2
  have hxP : x ∉ P := fun h => ((hPmem x).mp h).2 hxy.symm
  have hyP : y ∉ P := fun h => ((hPmem y).mp h).1 hxy
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]; intro v hvA hvC
    exact ((hAmem v).mp hvA).2.1 ((hCmem v).mp hvC).2
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]; intro v hvA hvB
    exact ((hAmem v).mp hvA).2.1 ((hBmem v).mp hvB).1
  have hAP : Disjoint A P := by
    rw [Finset.disjoint_left]; intro v hvA hvP
    exact ((hPmem v).mp hvP).1 ((hAmem v).mp hvA).1
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]; intro v hvB hvC
    exact ((hBmem v).mp hvB).2.1 ((hCmem v).mp hvC).1
  have hBP : Disjoint B P := by
    rw [Finset.disjoint_left]; intro v hvB hvP
    exact ((hPmem v).mp hvP).2 ((hBmem v).mp hvB).1
  have hCP : Disjoint C P := by
    rw [Finset.disjoint_left]; intro v hvC hvP
    exact ((hPmem v).mp hvP).1 ((hCmem v).mp hvC).1
  have hxy_disj_sing : Disjoint ({x} : Finset V) {y} := by
    rw [Finset.disjoint_singleton_left]
    simpa using hxyne
  have hxy_A : Disjoint ({x} ∪ {y} : Finset V) A := by
    rw [Finset.disjoint_union_left]
    exact ⟨by rwa [Finset.disjoint_singleton_left], by rwa [Finset.disjoint_singleton_left]⟩
  have hxy_B : Disjoint ({x} ∪ {y} : Finset V) B := by
    rw [Finset.disjoint_union_left]
    exact ⟨by rwa [Finset.disjoint_singleton_left], by rwa [Finset.disjoint_singleton_left]⟩
  have hxy_C : Disjoint ({x} ∪ {y} : Finset V) C := by
    rw [Finset.disjoint_union_left]
    exact ⟨by rwa [Finset.disjoint_singleton_left], by rwa [Finset.disjoint_singleton_left]⟩
  have hxy_P : Disjoint ({x} ∪ {y} : Finset V) P := by
    rw [Finset.disjoint_union_left]
    exact ⟨by rwa [Finset.disjoint_singleton_left], by rwa [Finset.disjoint_singleton_left]⟩
  have hACy : Disjoint (A ∪ C) ({y} : Finset V) := by
    rw [Finset.disjoint_union_left]
    exact ⟨by rwa [Finset.disjoint_singleton_right], by rwa [Finset.disjoint_singleton_right]⟩
  have hBCx : Disjoint (B ∪ C) ({x} : Finset V) := by
    rw [Finset.disjoint_union_left]
    exact ⟨by rwa [Finset.disjoint_singleton_right], by rwa [Finset.disjoint_singleton_right]⟩
  have hNx : G.neighborFinset x = A ∪ C ∪ {y} := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hv
      by_cases hvy : v = y
      · exact Or.inr hvy
      · by_cases hyv : G.Adj y v
        · exact Or.inl (Or.inr ((hCmem v).mpr ⟨hv, hyv⟩))
        · exact Or.inl (Or.inl ((hAmem v).mpr ⟨hv, hyv, hvy⟩))
    · rintro ((hvA | hvC) | hvy)
      · exact ((hAmem v).mp hvA).1
      · exact ((hCmem v).mp hvC).1
      · rw [hvy]; exact hxy
  have hNy : G.neighborFinset y = B ∪ C ∪ {x} := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hv
      by_cases hvx : v = x
      · exact Or.inr hvx
      · by_cases hxv : G.Adj x v
        · exact Or.inl (Or.inr ((hCmem v).mpr ⟨hxv, hv⟩))
        · exact Or.inl (Or.inl ((hBmem v).mpr ⟨hv, hxv, hvx⟩))
    · rintro ((hvB | hvC) | hvx)
      · exact ((hBmem v).mp hvB).1
      · exact ((hCmem v).mp hvC).2
      · rw [hvx]; exact hxy.symm
  have hdegx : G.degree x = A.card + C.card + 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hNx,
      Finset.card_union_of_disjoint hACy, Finset.card_union_of_disjoint hAC,
      Finset.card_singleton]
  have hdegy : G.degree y = B.card + C.card + 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hNy,
      Finset.card_union_of_disjoint hBCx, Finset.card_union_of_disjoint hBC,
      Finset.card_singleton]
  have d2 : Disjoint (({x} ∪ {y}) ∪ A : Finset V) B := by
    rw [Finset.disjoint_union_left]; exact ⟨hxy_B, hAB⟩
  have d3 : Disjoint ((({x} ∪ {y}) ∪ A) ∪ B : Finset V) C := by
    rw [Finset.disjoint_union_left]
    refine ⟨?_, hBC⟩
    rw [Finset.disjoint_union_left]; exact ⟨hxy_C, hAC⟩
  have d4 : Disjoint (((({x} ∪ {y}) ∪ A) ∪ B) ∪ C : Finset V) P := by
    rw [Finset.disjoint_union_left]
    refine ⟨?_, hCP⟩
    rw [Finset.disjoint_union_left]
    refine ⟨?_, hBP⟩
    rw [Finset.disjoint_union_left]; exact ⟨hxy_P, hAP⟩
  have hcard : Fintype.card V = 2 + A.card + B.card + C.card + P.card := by
    rw [← Finset.card_univ, hcover,
      Finset.card_union_of_disjoint d4, Finset.card_union_of_disjoint d3,
      Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint hxy_A,
      Finset.card_union_of_disjoint hxy_disj_sing, Finset.card_singleton,
      Finset.card_singleton]
  exact ⟨hdegx, hdegy, hcard⟩
