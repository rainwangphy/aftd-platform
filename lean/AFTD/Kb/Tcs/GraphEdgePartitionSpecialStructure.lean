import AFTD.Prelude
import AFTD.Kb.Tcs.GraphEdgePartitionCard

/-!
# graph_edge_partition_special_structure

Topic: graphs   Node: dd3a71716fe9

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

If in the edge partition |B| = |C| + 2 and deg x = deg y, then P = ∅, |A| = |B|, and there is an edge between A and B.
-/

/-- In the boundary configuration (equal degrees, |B| = |C|+2) the leftover part P is empty, |A| = |B|, and some A-vertex is adjacent to some B-vertex. -/
theorem graph_edge_partition_special_structure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hδ : (2 * (Fintype.card V : ℝ)) / 3 - 1 ≤ (G.minDegree : ℝ))
    (x y : V) (A B C P : Finset V)
    (hAmem : ∀ v, v ∈ A ↔ (G.Adj x v ∧ ¬ G.Adj y v ∧ v ≠ y))
    (hBmem : ∀ v, v ∈ B ↔ (G.Adj y v ∧ ¬ G.Adj x v ∧ v ≠ x))
    (hCmem : ∀ v, v ∈ C ↔ (G.Adj x v ∧ G.Adj y v))
    (hPmem : ∀ v, v ∈ P ↔ (¬ G.Adj x v ∧ ¬ G.Adj y v))
    (hcover : (Finset.univ : Finset V) = {x} ∪ {y} ∪ A ∪ B ∪ C ∪ P)
    (hdx : G.degree x = A.card + C.card + 1)
    (hdy : G.degree y = B.card + C.card + 1)
    (hn : Fintype.card V = 2 + A.card + B.card + C.card + P.card)
    (heq : G.degree x = G.degree y) (hb : B.card = C.card + 2) :
    P = ∅ ∧ A.card = B.card ∧ (∃ v ∈ A, ∃ u ∈ B, G.Adj v u) := by
  have hAeqB : A.card = B.card := by omega
  have hnR : (Fintype.card V : ℝ) = 2 + (A.card:ℝ) + (B.card:ℝ) + (C.card:ℝ) + (P.card:ℝ) := by
    rw [hn]; push_cast; ring
  have hdyR : (G.degree y : ℝ) = (B.card:ℝ) + (C.card:ℝ) + 1 := by rw [hdy]; push_cast; ring
  have hAbR : (A.card:ℝ) = (B.card:ℝ) := by exact_mod_cast hAeqB
  have hbR : (B.card:ℝ) = (C.card:ℝ) + 2 := by exact_mod_cast hb
  have hminy : (G.minDegree : ℝ) ≤ (G.degree y : ℝ) := by
    exact_mod_cast SimpleGraph.minDegree_le_degree G y
  have hP0R : (P.card:ℝ) ≤ 0 := by nlinarith [hδ, hminy, hnR, hdyR, hAbR, hbR]
  have hP0 : P.card = 0 := by
    have h : P.card ≤ 0 := by exact_mod_cast hP0R
    omega
  have hPempty : P = ∅ := Finset.card_eq_zero.mp hP0
  refine ⟨hPempty, hAeqB, ?_⟩
  by_contra hno
  push Not at hno
  have hBcard : 0 < B.card := by omega
  obtain ⟨u, huB⟩ := Finset.card_pos.mp hBcard
  have hux : ¬ G.Adj x u := ((hBmem u).mp huB).2.1
  have hsub : G.neighborFinset u ⊆ ({y} ∪ (B.erase u ∪ C) : Finset V) := by
    intro v hv
    rw [SimpleGraph.mem_neighborFinset] at hv
    have hvuniv : v ∈ ({x} ∪ {y} ∪ A ∪ B ∪ C ∪ P : Finset V) := by
      rw [← hcover]; exact Finset.mem_univ v
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase] at hvuniv ⊢
    rcases hvuniv with ((((hx | hy) | hA) | hB) | hC) | hP
    · subst hx; exact absurd hv.symm hux
    · exact Or.inl hy
    · exact absurd hv.symm (hno v hA u huB)
    · exact Or.inr (Or.inl ⟨(G.ne_of_adj hv).symm, hB⟩)
    · exact Or.inr (Or.inr hC)
    · rw [hPempty] at hP; simp at hP
  have hyB : y ∉ B := fun h => G.irrefl ((hBmem y).mp h).1
  have hyC : y ∉ C := fun h => G.irrefl ((hCmem y).mp h).2
  have hBCdisj : Disjoint B C := by
    rw [Finset.disjoint_left]; intro v hvB hvC
    exact ((hBmem v).mp hvB).2.1 ((hCmem v).mp hvC).1
  have hd1 : Disjoint ({y} : Finset V) (B.erase u ∪ C) := by
    rw [Finset.disjoint_union_right, Finset.disjoint_singleton_left, Finset.disjoint_singleton_left]
    refine ⟨?_, hyC⟩
    intro h; exact hyB (Finset.mem_of_mem_erase h)
  have hd2 : Disjoint (B.erase u) C := by
    rw [Finset.disjoint_left]; intro v hv hvC
    exact (Finset.disjoint_left.mp hBCdisj) (Finset.mem_of_mem_erase hv) hvC
  have hcardS : ({y} ∪ (B.erase u ∪ C) : Finset V).card = B.card + C.card := by
    rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
        Finset.card_singleton, Finset.card_erase_of_mem huB]
    omega
  have hdeg_le : G.degree u ≤ B.card + C.card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact le_trans (Finset.card_le_card hsub) (le_of_eq hcardS)
  have hdegUR : (G.degree u : ℝ) ≤ (B.card:ℝ) + (C.card:ℝ) := by exact_mod_cast hdeg_le
  have hminu : (G.minDegree : ℝ) ≤ (G.degree u : ℝ) := by
    exact_mod_cast SimpleGraph.minDegree_le_degree G u
  have hPcardR : (P.card : ℝ) = 0 := by rw [hP0]; simp
  nlinarith [hδ, hminu, hdegUR, hnR, hAbR, hbR, hPcardR]
