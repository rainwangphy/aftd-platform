import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.BoundaryFiveBlocksEssentialEdgeCrossDefectPattern
import AFTD.Kb.Tcs.FiveByFiveSparseDefectsHaveGoodPair
import AFTD.Kb.Tcs.BoundaryFiveBlocksMinimalNoFullCross
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound
import AFTD.Kb.Tcs.IsKExtendable

/-!
# minimally_k_extendable_five_block_boundary_degree_bound_with_separator

Topic: graphs   Node: 195dd4d77a10

Provenance: original. Related work: OP-1957; the associated four-block boundary structure is in arXiv:1011.3384, Theorem 2.1. This result explicitly assumes the separator property and that both selected blocks have size five.

For every natural number k at least five, let G be a connected minimally k-extendible simple graph on Fin (4k) with decidable adjacency. Let A, B, C, D be pairwise disjoint sets covering all vertices, with |A|=|C|=5, |A|+|B|=|C|+|D|=2k, no edges between A and B, and no edges between C and D. Assume that every partition of all vertices into pairwise disjoint sets X, U, V, with U and V nonempty and anticomplete to each other, satisfies |X|≥2k. Then some vertex of G has degree at most 2k+1.
-/

theorem minimally_k_extendable_five_block_boundary_degree_bound_with_separator
    (k : ℕ) (hk : 5 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : is_minimally_k_extendable G k)
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hC : C.card=5)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    : ∃ v, (G.neighborFinset v).card ≤ 2*k+1 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card := by
    intro v
    have h := hnone v
    omega
  have hrowupper : ∀ a ∈ A, (C.filter (fun c => ¬ G.Adj a c)).card ≤ 2 := by
    intro a ha
    have haB : a ∉ B := fun h => Finset.disjoint_left.mp hAB ha h
    have hh := anticomplete_neighbor_defect_bound G B a haB (hnoAB a ha)
      (2*k+4) 2 (by simp; omega) (by have := hdegree a; omega)
    apply le_trans (Finset.card_le_card ?_) hh
    intro c hc
    simp only [Finset.mem_filter] at hc
    have hcB : c ∉ B := fun h => Finset.disjoint_left.mp hBC h hc.1
    have hca : c ≠ a := fun h => Finset.disjoint_left.mp hAC ha (h ▸ hc.1)
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hca,hcB⟩,hc.2⟩
  have hcolupper : ∀ c ∈ C, (A.filter (fun a => ¬ G.Adj a c)).card ≤ 2 := by
    intro c hc
    have hcD : c ∉ D := fun h => Finset.disjoint_left.mp hCD hc h
    have hh := anticomplete_neighbor_defect_bound G D c hcD (hnoCD c hc)
      (2*k+4) 2 (by simp; omega) (by have := hdegree c; omega)
    apply le_trans (Finset.card_le_card ?_) hh
    intro a ha
    simp only [Finset.mem_filter] at ha
    have haD : a ∉ D := fun h => Finset.disjoint_left.mp hAD ha.1 h
    have hac : a ≠ c := fun h => Finset.disjoint_left.mp hAC ha.1 (h ▸ hc)
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hac,haD⟩,fun h => ha.2 h.symm⟩
  have hrowlower := boundary_five_blocks_minimal_no_full_cross k hk G A B C D
    hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoAB hnoCD hdegree hsep hmin
  have hcover' : C ∪ D ∪ A ∪ B = Finset.univ := by
    calc
      C ∪ D ∪ A ∪ B = A ∪ B ∪ C ∪ D := by ac_rfl
      _ = Finset.univ := hcover
  have hcollo' := boundary_five_blocks_minimal_no_full_cross k hk G C D A B
    hCD hAC.symm hBC.symm hAD.symm hBD.symm hAB hcover' hC hA hsizeCD hsizeAB
    hnoCD hnoAB hdegree hsep hmin
  have hcollower : ∀ c ∈ C, 1 ≤ (A.filter (fun a => ¬ G.Adj a c)).card := by
    intro c hc
    have heq : A.filter (fun a => ¬ G.Adj c a) = A.filter (fun a => ¬ G.Adj a c) := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ha,hn⟩; exact ⟨ha,fun h => hn h.symm⟩
      · rintro ⟨ha,hn⟩; exact ⟨ha,fun h => hn h.symm⟩
    simpa only [heq] using hcollo' c hc
  have hno22 : ∀ a ∈ A, ∀ c ∈ C, ¬ G.Adj a c →
      (C.filter (fun y => ¬ G.Adj a y)).card = 2 →
      (A.filter (fun v => ¬ G.Adj v c)).card ≠ 2 := by
    intro a ha c hc hac ha2 hc2
    have hex : ∃ y ∈ C, G.Adj a y := by
      by_contra hn
      push_neg at hn
      have heq : C.filter (fun y => ¬ G.Adj a y) = C := by
        ext y
        simp only [Finset.mem_filter]
        exact ⟨And.left, fun hy => ⟨hy,hn y hy⟩⟩
      rw [heq,hC] at ha2
      omega
    obtain ⟨y,hy,hay⟩ := hex
    have he : ¬ is_k_extendable (G.deleteEdges {s(a,y)}) k :=
      hmin.2 s(a,y) (by simpa using hay)
    have hp := boundary_five_blocks_essential_edge_cross_defect_pattern k hk G A B C D
      hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoAB hnoCD hdegree hsep
      hmin.1 a y ha hy hay he
    have hh := hp.1 ha2 c hc hac
    omega
  obtain ⟨a,ha,c,hc,hn,ha1,hc1⟩ := five_by_five_sparse_defects_have_good_pair A C
    (fun a c => ¬ G.Adj a c) hA hC
    (fun a ha => ⟨hrowlower a ha,hrowupper a ha⟩)
    (fun c hc => ⟨hcollower c hc,hcolupper c hc⟩) hno22
  have hac : G.Adj a c := Classical.not_not.mp hn
  have he : ¬ is_k_extendable (G.deleteEdges {s(a,c)}) k :=
    hmin.2 s(a,c) (by simpa using hac)
  have hp := boundary_five_blocks_essential_edge_cross_defect_pattern k hk G A B C D
    hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoAB hnoCD hdegree hsep
    hmin.1 a c ha hc hac he
  have hh := hp.2 (by omega)
  omega
