import AFTD.Prelude
import AFTD.Kb.Tcs.IsNonsustainableTree
import AFTD.Kb.Tcs.IsSustainableEdge
import AFTD.Kb.Tcs.IsTreeIffIsAcyclicAndCard
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.AdjacencySpectralRadius
import AFTD.Kb.Tcs.IsSustainableTree
import AFTD.Kb.Tcs.G

/-!
# op223_no_nonsustainable_tree_fin_three

Topic: graphs   Node: 8007da4f94c8

Provenance: helper lemma. arXiv:2610.17078, Section 3

There are no non-sustainable trees on three vertices.
-/

abbrev op223_no_nonsustainable_tree_fin_three_GA : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet (↑({s(0,1), s(1,2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))
abbrev op223_no_nonsustainable_tree_fin_three_GB : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet (↑({s(0,1), s(0,2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))
abbrev op223_no_nonsustainable_tree_fin_three_GC : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet (↑({s(1,2), s(0,2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))

lemma op223_no_nonsustainable_tree_fin_three_rad_iso {V W : Type*} [Fintype V]
    [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    adjacency_spectral_radius G = adjacency_spectral_radius H := by
  classical
  unfold adjacency_spectral_radius spectralRadius
  have hmat :
      (Matrix.reindex (e : V ≃ W) (e : V ≃ W)) (SimpleGraph.adjMatrix ℝ G) =
        SimpleGraph.adjMatrix ℝ H :=
    SimpleGraph.Iso.reindex_adjMatrix ℝ e
  have hsp :=
    AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℝ (e : V ≃ W)) (SimpleGraph.adjMatrix ℝ G)
  simp only [Matrix.coe_reindexAlgEquiv] at hsp
  rw [← hsp, hmat]

def op223_no_nonsustainable_tree_fin_three_iso_AB :
    op223_no_nonsustainable_tree_fin_three_GA ≃g op223_no_nonsustainable_tree_fin_three_GB :=
  RelIso.mk (toEquiv := Equiv.swap 0 1)
    (by
      intro a b
      fin_cases a <;> fin_cases b <;>
        simp [op223_no_nonsustainable_tree_fin_three_GA,
          op223_no_nonsustainable_tree_fin_three_GB, SimpleGraph.fromEdgeSet_adj] <;> decide)

def op223_no_nonsustainable_tree_fin_three_iso_AC :
    op223_no_nonsustainable_tree_fin_three_GA ≃g op223_no_nonsustainable_tree_fin_three_GC :=
  RelIso.mk (toEquiv := Equiv.swap 1 2)
    (by
      intro a b
      fin_cases a <;> fin_cases b <;>
        simp [op223_no_nonsustainable_tree_fin_three_GA,
          op223_no_nonsustainable_tree_fin_three_GC, SimpleGraph.fromEdgeSet_adj] <;> decide)

lemma op223_no_nonsustainable_tree_fin_three_rad_AB :
    adjacency_spectral_radius op223_no_nonsustainable_tree_fin_three_GA =
      adjacency_spectral_radius op223_no_nonsustainable_tree_fin_three_GB :=
  op223_no_nonsustainable_tree_fin_three_rad_iso op223_no_nonsustainable_tree_fin_three_iso_AB

lemma op223_no_nonsustainable_tree_fin_three_rad_AC :
    adjacency_spectral_radius op223_no_nonsustainable_tree_fin_three_GA =
      adjacency_spectral_radius op223_no_nonsustainable_tree_fin_three_GC :=
  op223_no_nonsustainable_tree_fin_three_rad_iso op223_no_nonsustainable_tree_fin_three_iso_AC

lemma op223_no_nonsustainable_tree_fin_three_edgeSet_of_pair (a b : Sym2 (Fin 3))
    (ha : ¬ a.IsDiag) (hb : ¬ b.IsDiag) :
    ((SimpleGraph.fromEdgeSet (↑({a, b} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))).edgeSet)
      = (({a, b} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))) := by
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_sdiff, Finset.mem_coe]
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h
    refine ⟨h, ?_⟩
    rw [Sym2.mem_diagSet]
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact ha
    · exact hb

lemma op223_no_nonsustainable_tree_fin_three_edgeSet_A :
    op223_no_nonsustainable_tree_fin_three_GA.edgeSet =
      (({s(0,1), s(1,2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))) :=
  op223_no_nonsustainable_tree_fin_three_edgeSet_of_pair _
    _ (by rw [Sym2.mk_isDiag_iff]; decide) (by rw [Sym2.mk_isDiag_iff]; decide)

lemma op223_no_nonsustainable_tree_fin_three_edgeSet_B :
    op223_no_nonsustainable_tree_fin_three_GB.edgeSet =
      (({s(0,1), s(0,2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))) :=
  op223_no_nonsustainable_tree_fin_three_edgeSet_of_pair _
    _ (by rw [Sym2.mk_isDiag_iff]; decide) (by rw [Sym2.mk_isDiag_iff]; decide)

lemma op223_no_nonsustainable_tree_fin_three_edgeSet_C :
    op223_no_nonsustainable_tree_fin_three_GC.edgeSet =
      (({s(1,2), s(0,2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))) :=
  op223_no_nonsustainable_tree_fin_three_edgeSet_of_pair _
    _ (by rw [Sym2.mk_isDiag_iff]; decide) (by rw [Sym2.mk_isDiag_iff]; decide)

lemma op223_no_nonsustainable_tree_fin_three_sw_A_p01 :
    op223_no_nonsustainable_tree_fin_three_GA.deleteEdges {s(0,1)} ⊔
        SimpleGraph.fromEdgeSet {s(0,2)} = op223_no_nonsustainable_tree_fin_three_GC := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [op223_no_nonsustainable_tree_fin_three_GA,
      op223_no_nonsustainable_tree_fin_three_GC, SimpleGraph.fromEdgeSet_adj, SimpleGraph.sup_adj]

lemma op223_no_nonsustainable_tree_fin_three_sw_A_p12 :
    op223_no_nonsustainable_tree_fin_three_GA.deleteEdges {s(1,2)} ⊔
        SimpleGraph.fromEdgeSet {s(0,2)} = op223_no_nonsustainable_tree_fin_three_GB := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [op223_no_nonsustainable_tree_fin_three_GA,
      op223_no_nonsustainable_tree_fin_three_GB, SimpleGraph.fromEdgeSet_adj, SimpleGraph.sup_adj]

lemma op223_no_nonsustainable_tree_fin_three_sw_B_p01 :
    op223_no_nonsustainable_tree_fin_three_GB.deleteEdges {s(0,1)} ⊔
        SimpleGraph.fromEdgeSet {s(1,2)} = op223_no_nonsustainable_tree_fin_three_GC := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [op223_no_nonsustainable_tree_fin_three_GB,
      op223_no_nonsustainable_tree_fin_three_GC, SimpleGraph.fromEdgeSet_adj, SimpleGraph.sup_adj]

lemma op223_no_nonsustainable_tree_fin_three_sw_B_p02 :
    op223_no_nonsustainable_tree_fin_three_GB.deleteEdges {s(0,2)} ⊔
        SimpleGraph.fromEdgeSet {s(1,2)} = op223_no_nonsustainable_tree_fin_three_GA := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [op223_no_nonsustainable_tree_fin_three_GA,
      op223_no_nonsustainable_tree_fin_three_GB, SimpleGraph.fromEdgeSet_adj, SimpleGraph.sup_adj]

lemma op223_no_nonsustainable_tree_fin_three_sw_C_p12 :
    op223_no_nonsustainable_tree_fin_three_GC.deleteEdges {s(1,2)} ⊔
        SimpleGraph.fromEdgeSet {s(0,1)} = op223_no_nonsustainable_tree_fin_three_GB := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [op223_no_nonsustainable_tree_fin_three_GB,
      op223_no_nonsustainable_tree_fin_three_GC, SimpleGraph.fromEdgeSet_adj, SimpleGraph.sup_adj]

lemma op223_no_nonsustainable_tree_fin_three_sw_C_p02 :
    op223_no_nonsustainable_tree_fin_three_GC.deleteEdges {s(0,2)} ⊔
        SimpleGraph.fromEdgeSet {s(0,1)} = op223_no_nonsustainable_tree_fin_three_GA := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [op223_no_nonsustainable_tree_fin_three_GA,
      op223_no_nonsustainable_tree_fin_three_GC, SimpleGraph.fromEdgeSet_adj, SimpleGraph.sup_adj]

lemma op223_no_nonsustainable_tree_fin_three_sust_of_swap {G H : SimpleGraph (Fin 3)}
    {e f : Sym2 (Fin 3)} (he : e ∈ G.edgeSet) (hf : f ∈ Gᶜ.edgeSet)
    (hsw : G.deleteEdges {e} ⊔ SimpleGraph.fromEdgeSet {f} = H)
    (hH : H.IsTree) (hr : adjacency_spectral_radius G ≤ adjacency_spectral_radius H) :
    is_sustainable_edge G e :=
  ⟨he, f, hf, by rw [hsw]; exact hH, by rw [hsw]; exact hr⟩

lemma op223_no_nonsustainable_tree_fin_three_sust_A_p01
    (hC : op223_no_nonsustainable_tree_fin_three_GC.IsTree) :
    is_sustainable_edge op223_no_nonsustainable_tree_fin_three_GA s(0,1) :=
  op223_no_nonsustainable_tree_fin_three_sust_of_swap
    (by rw [SimpleGraph.mem_edgeSet];
        simp [op223_no_nonsustainable_tree_fin_three_GA, SimpleGraph.fromEdgeSet_adj])
    (by rw [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj]
        exact ⟨by decide,
          by simp [op223_no_nonsustainable_tree_fin_three_GA, SimpleGraph.fromEdgeSet_adj]⟩)
    op223_no_nonsustainable_tree_fin_three_sw_A_p01 hC
    (le_of_eq op223_no_nonsustainable_tree_fin_three_rad_AC)

lemma op223_no_nonsustainable_tree_fin_three_sust_A_p12
    (hB : op223_no_nonsustainable_tree_fin_three_GB.IsTree) :
    is_sustainable_edge op223_no_nonsustainable_tree_fin_three_GA s(1,2) :=
  op223_no_nonsustainable_tree_fin_three_sust_of_swap
    (by rw [SimpleGraph.mem_edgeSet];
        simp [op223_no_nonsustainable_tree_fin_three_GA, SimpleGraph.fromEdgeSet_adj])
    (by rw [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj]
        exact ⟨by decide,
          by simp [op223_no_nonsustainable_tree_fin_three_GA, SimpleGraph.fromEdgeSet_adj]⟩)
    op223_no_nonsustainable_tree_fin_three_sw_A_p12 hB
    (le_of_eq op223_no_nonsustainable_tree_fin_three_rad_AB)

lemma op223_no_nonsustainable_tree_fin_three_sust_B_p01
    (hC : op223_no_nonsustainable_tree_fin_three_GC.IsTree) :
    is_sustainable_edge op223_no_nonsustainable_tree_fin_three_GB s(0,1) :=
  op223_no_nonsustainable_tree_fin_three_sust_of_swap
    (by rw [SimpleGraph.mem_edgeSet];
        simp [op223_no_nonsustainable_tree_fin_three_GB, SimpleGraph.fromEdgeSet_adj])
    (by rw [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj]
        exact ⟨by decide,
          by simp [op223_no_nonsustainable_tree_fin_three_GB, SimpleGraph.fromEdgeSet_adj]⟩)
    op223_no_nonsustainable_tree_fin_three_sw_B_p01 hC
    (by rw [← op223_no_nonsustainable_tree_fin_three_rad_AB,
      op223_no_nonsustainable_tree_fin_three_rad_AC])

lemma op223_no_nonsustainable_tree_fin_three_sust_B_p02
    (hA : op223_no_nonsustainable_tree_fin_three_GA.IsTree) :
    is_sustainable_edge op223_no_nonsustainable_tree_fin_three_GB s(0,2) :=
  op223_no_nonsustainable_tree_fin_three_sust_of_swap
    (by rw [SimpleGraph.mem_edgeSet];
        simp [op223_no_nonsustainable_tree_fin_three_GB, SimpleGraph.fromEdgeSet_adj])
    (by rw [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj]
        exact ⟨by decide,
          by simp [op223_no_nonsustainable_tree_fin_three_GB, SimpleGraph.fromEdgeSet_adj]⟩)
    op223_no_nonsustainable_tree_fin_three_sw_B_p02 hA
    (le_of_eq op223_no_nonsustainable_tree_fin_three_rad_AB.symm)

lemma op223_no_nonsustainable_tree_fin_three_sust_C_p12
    (hB : op223_no_nonsustainable_tree_fin_three_GB.IsTree) :
    is_sustainable_edge op223_no_nonsustainable_tree_fin_three_GC s(1,2) :=
  op223_no_nonsustainable_tree_fin_three_sust_of_swap
    (by rw [SimpleGraph.mem_edgeSet];
        simp [op223_no_nonsustainable_tree_fin_three_GC, SimpleGraph.fromEdgeSet_adj])
    (by rw [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj]
        exact ⟨by decide,
          by simp [op223_no_nonsustainable_tree_fin_three_GC, SimpleGraph.fromEdgeSet_adj]⟩)
    op223_no_nonsustainable_tree_fin_three_sw_C_p12 hB
    (by rw [← op223_no_nonsustainable_tree_fin_three_rad_AC,
      op223_no_nonsustainable_tree_fin_three_rad_AB])

lemma op223_no_nonsustainable_tree_fin_three_sust_C_p02
    (hA : op223_no_nonsustainable_tree_fin_three_GA.IsTree) :
    is_sustainable_edge op223_no_nonsustainable_tree_fin_three_GC s(0,2) :=
  op223_no_nonsustainable_tree_fin_three_sust_of_swap
    (by rw [SimpleGraph.mem_edgeSet];
        simp [op223_no_nonsustainable_tree_fin_three_GC, SimpleGraph.fromEdgeSet_adj])
    (by rw [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj]
        exact ⟨by decide,
          by simp [op223_no_nonsustainable_tree_fin_three_GC, SimpleGraph.fromEdgeSet_adj]⟩)
    op223_no_nonsustainable_tree_fin_three_sw_C_p02 hA
    (le_of_eq op223_no_nonsustainable_tree_fin_three_rad_AC.symm)

lemma op223_no_nonsustainable_tree_fin_three_two_subset :
    ∀ S : Finset (Sym2 (Fin 3)),
      S ⊆ ({s(0,1), s(1,2), s(0,2)} : Finset (Sym2 (Fin 3))) → S.card = 2 →
      S = ({s(0,1), s(1,2)} : Finset (Sym2 (Fin 3))) ∨
      S = ({s(0,1), s(0,2)} : Finset (Sym2 (Fin 3))) ∨
      S = ({s(1,2), s(0,2)} : Finset (Sym2 (Fin 3))) := by
  decide

/-- On three vertices, no simple graph is a non-sustainable tree. -/
theorem op223_no_nonsustainable_tree_fin_three (X : SimpleGraph (Fin 3)) :
    ¬ is_nonsustainable_tree X := by
  classical
  rintro ⟨hXtree, hnsus⟩
  apply hnsus
  refine ⟨hXtree, ?_⟩
  have hcard : Nat.card X.edgeSet = 2 := by
    have h1 := (is_tree_iff_is_acyclic_and_card X).mp hXtree
    have h3 : Nat.card (Fin 3) = 3 := by simp
    omega
  have hsub : X.edgeSet ⊆
      (↑({s(0,1), s(1,2), s(0,2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      have hab : a ≠ b := by intro h; subst h; simp at he
      fin_cases a <;> fin_cases b <;> simp_all
  have hfin : X.edgeSet.Finite := Set.toFinite X.edgeSet
  set S := hfin.toFinset with hSdef
  have hSsub : S ⊆ ({s(0,1), s(1,2), s(0,2)} : Finset (Sym2 (Fin 3))) := by
    intro x hx
    have hx' : x ∈ X.edgeSet := (Set.Finite.mem_toFinset hfin).mp (by rw [hSdef] at hx; exact hx)
    simpa using hsub hx'
  have hScard : S.card = 2 := by
    rw [hSdef, ← Set.ncard_eq_toFinset_card X.edgeSet hfin, ← Nat.card_coe_set_eq]
    exact hcard
  have hXedges : X.edgeSet = ↑S := by rw [hSdef, Set.Finite.coe_toFinset hfin]
  rcases op223_no_nonsustainable_tree_fin_three_two_subset S hSsub hScard with hA | hB | hC
  · have hstep : SimpleGraph.fromEdgeSet X.edgeSet = op223_no_nonsustainable_tree_fin_three_GA := by
      rw [hXedges, hA]
    have hXeqA : X = op223_no_nonsustainable_tree_fin_three_GA :=
      (SimpleGraph.fromEdgeSet_edgeSet X).symm.trans hstep
    have hGA : op223_no_nonsustainable_tree_fin_three_GA.IsTree := hXeqA ▸ hXtree
    have hGB : op223_no_nonsustainable_tree_fin_three_GB.IsTree :=
      op223_no_nonsustainable_tree_fin_three_iso_AB.isTree_iff.mp hGA
    have hGC : op223_no_nonsustainable_tree_fin_three_GC.IsTree :=
      op223_no_nonsustainable_tree_fin_three_iso_AC.isTree_iff.mp hGA
    rw [hXeqA]
    intro e he
    have hmem : e = s(0,1) ∨ e = s(1,2) := by
      have h2 := he
      rw [op223_no_nonsustainable_tree_fin_three_edgeSet_A] at h2
      simpa [Finset.mem_insert, Finset.mem_singleton] using h2
    rcases hmem with rfl | rfl
    · exact op223_no_nonsustainable_tree_fin_three_sust_A_p01 hGC
    · exact op223_no_nonsustainable_tree_fin_three_sust_A_p12 hGB
  · have hstep : SimpleGraph.fromEdgeSet X.edgeSet = op223_no_nonsustainable_tree_fin_three_GB := by
      rw [hXedges, hB]
    have hXeqB : X = op223_no_nonsustainable_tree_fin_three_GB :=
      (SimpleGraph.fromEdgeSet_edgeSet X).symm.trans hstep
    have hGB : op223_no_nonsustainable_tree_fin_three_GB.IsTree := hXeqB ▸ hXtree
    have hGA : op223_no_nonsustainable_tree_fin_three_GA.IsTree :=
      op223_no_nonsustainable_tree_fin_three_iso_AB.isTree_iff.mpr hGB
    have hGC : op223_no_nonsustainable_tree_fin_three_GC.IsTree :=
      op223_no_nonsustainable_tree_fin_three_iso_AC.isTree_iff.mp hGA
    rw [hXeqB]
    intro e he
    have hmem : e = s(0,1) ∨ e = s(0,2) := by
      have h2 := he
      rw [op223_no_nonsustainable_tree_fin_three_edgeSet_B] at h2
      simpa [Finset.mem_insert, Finset.mem_singleton] using h2
    rcases hmem with rfl | rfl
    · exact op223_no_nonsustainable_tree_fin_three_sust_B_p01 hGC
    · exact op223_no_nonsustainable_tree_fin_three_sust_B_p02 hGA
  · have hstep : SimpleGraph.fromEdgeSet X.edgeSet = op223_no_nonsustainable_tree_fin_three_GC := by
      rw [hXedges, hC]
    have hXeqC : X = op223_no_nonsustainable_tree_fin_three_GC :=
      (SimpleGraph.fromEdgeSet_edgeSet X).symm.trans hstep
    have hGC : op223_no_nonsustainable_tree_fin_three_GC.IsTree := hXeqC ▸ hXtree
    have hGA : op223_no_nonsustainable_tree_fin_three_GA.IsTree :=
      op223_no_nonsustainable_tree_fin_three_iso_AC.isTree_iff.mpr hGC
    have hGB : op223_no_nonsustainable_tree_fin_three_GB.IsTree :=
      op223_no_nonsustainable_tree_fin_three_iso_AB.isTree_iff.mp hGA
    rw [hXeqC]
    intro e he
    have hmem : e = s(1,2) ∨ e = s(0,2) := by
      have h2 := he
      rw [op223_no_nonsustainable_tree_fin_three_edgeSet_C] at h2
      simpa [Finset.mem_insert, Finset.mem_singleton] using h2
    rcases hmem with rfl | rfl
    · exact op223_no_nonsustainable_tree_fin_three_sust_C_p12 hGB
    · exact op223_no_nonsustainable_tree_fin_three_sust_C_p02 hGA
