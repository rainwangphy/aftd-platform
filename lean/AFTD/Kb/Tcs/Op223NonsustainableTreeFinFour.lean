import AFTD.Prelude
import AFTD.Kb.Tcs.IsNonsustainableTree
import AFTD.Kb.Tcs.Op223TreeFinFourIsoPathOrStar
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.IsSustainableTree
import AFTD.Kb.Tcs.AdjacencySpectralRadius
import AFTD.Kb.Tcs.IsSustainableEdge
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.G

/-!
# op223_nonsustainable_tree_fin_four

Topic: graphs   Node: 70da5ffde5e1

Provenance: helper lemma. arXiv:2610.17078, Section 3

Every non-sustainable tree on four vertices is isomorphic to the star graph K_{1,3}.
-/

open SimpleGraph

theorem op223_nonsustainable_tree_fin_four_rad_iso {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    adjacency_spectral_radius G = adjacency_spectral_radius H := by
  classical
  dsimp [adjacency_spectral_radius, spectralRadius]
  have hmat := SimpleGraph.Iso.reindex_adjMatrix ℝ e
  have hsp := AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℝ e.toEquiv) (SimpleGraph.adjMatrix ℝ G)
  change (Matrix.reindex e.toEquiv e.toEquiv) (SimpleGraph.adjMatrix ℝ G) = _ at hmat
  have hsp2 : (Matrix.reindexAlgEquiv ℝ ℝ e.toEquiv) (SimpleGraph.adjMatrix ℝ G) =
      (Matrix.reindex e.toEquiv e.toEquiv) (SimpleGraph.adjMatrix ℝ G) := rfl
  rw [hsp2, hmat] at hsp
  rw [hsp]

def op223_nonsustainable_tree_fin_four_swapIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (iso : G ≃g H) (e f : Sym2 V) :
    (G.deleteEdges {e} ⊔ fromEdgeSet {f}) ≃g
    (H.deleteEdges {Sym2.map iso e} ⊔ fromEdgeSet {Sym2.map iso f}) where
  toEquiv := iso.toEquiv
  map_rel_iff' := by
    intro u v
    simp only [sup_adj, deleteEdges_adj, fromEdgeSet_adj, Set.mem_singleton_iff]
    have h1 : H.Adj (iso u) (iso v) ↔ G.Adj u v := iso.map_rel_iff
    have h2 : s(iso u, iso v) = Sym2.map (⇑iso) e ↔ s(u, v) = e := by
      rw [← Sym2.map_mk, (Sym2.map.injective iso.injective).eq_iff]
    have h3 : s(iso u, iso v) = Sym2.map (⇑iso) f ↔ s(u, v) = f := by
      rw [← Sym2.map_mk, (Sym2.map.injective iso.injective).eq_iff]
    have h4 : iso u ≠ iso v ↔ u ≠ v := iso.injective.ne_iff
    tauto

theorem op223_nonsustainable_tree_fin_four_is_sustainable_edge_iso {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (iso : G ≃g H) (e : Sym2 V) (he : is_sustainable_edge G e) :
    is_sustainable_edge H (Sym2.map iso e) := by
  classical
  rcases he with ⟨he_edge, f, hf_nedge, htree, hrad⟩
  have he' : Sym2.map (⇑iso) e ∈ H.edgeSet := by
    induction e using Sym2.ind with
    | _ u v =>
      simp only [mem_edgeSet] at he_edge ⊢
      exact (iso.map_rel_iff).mpr he_edge
  refine ⟨he', Sym2.map (⇑iso) f, ?_, ?_, ?_⟩
  · induction f using Sym2.ind with
    | _ u v =>
      simp only [mem_edgeSet, compl_adj] at hf_nedge ⊢
      exact ⟨iso.injective.ne_iff.mpr hf_nedge.1, fun h => hf_nedge.2 (iso.map_rel_iff.mp h)⟩
  · have h_iso := op223_nonsustainable_tree_fin_four_swapIso iso e f
    exact h_iso.isTree_iff.mp htree
  · have hrad_G_H : adjacency_spectral_radius G = adjacency_spectral_radius H :=
      op223_nonsustainable_tree_fin_four_rad_iso iso
    have hrad_swap : adjacency_spectral_radius (G.deleteEdges {e} ⊔ fromEdgeSet {f}) =
        adjacency_spectral_radius (H.deleteEdges {Sym2.map iso e} ⊔ fromEdgeSet {Sym2.map iso f}) :=
      op223_nonsustainable_tree_fin_four_rad_iso (op223_nonsustainable_tree_fin_four_swapIso iso e f)
    rw [← hrad_G_H, ← hrad_swap]
    exact hrad

theorem op223_nonsustainable_tree_fin_four_is_sustainable_tree_iso {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (iso : G ≃g H) (hG : is_sustainable_tree G) :
    is_sustainable_tree H := by
  rcases hG with ⟨htree, hsust⟩
  refine ⟨iso.isTree_iff.mp htree, ?_⟩
  intro e he
  have he_pre : Sym2.map iso.symm e ∈ G.edgeSet := by
    induction e using Sym2.ind with
    | _ u v =>
      simp only [mem_edgeSet] at he ⊢
      exact iso.symm.map_rel_iff.mpr he
  have hsust_pre := hsust (Sym2.map iso.symm e) he_pre
  have h_map := op223_nonsustainable_tree_fin_four_is_sustainable_edge_iso iso (Sym2.map iso.symm e) hsust_pre
  have h_id : Sym2.map (⇑iso) (Sym2.map (⇑iso.symm) e) = e := by
    induction e using Sym2.ind with
    | _ u v => simp
  rwa [h_id] at h_map

def op223_nonsustainable_tree_fin_four_P4 : SimpleGraph (Fin 4) := pathGraph 4

def op223_nonsustainable_tree_fin_four_G1 : SimpleGraph (Fin 4) :=
  op223_nonsustainable_tree_fin_four_P4.deleteEdges {s(0, 1)} ⊔ fromEdgeSet {s(0, 3)}
def op223_nonsustainable_tree_fin_four_G2 : SimpleGraph (Fin 4) :=
  op223_nonsustainable_tree_fin_four_P4.deleteEdges {s(1, 2)} ⊔ fromEdgeSet {s(0, 2)}
def op223_nonsustainable_tree_fin_four_G3 : SimpleGraph (Fin 4) :=
  op223_nonsustainable_tree_fin_four_P4.deleteEdges {s(2, 3)} ⊔ fromEdgeSet {s(0, 3)}

lemma op223_nonsustainable_tree_fin_four_G1_adj (u v : Fin 4) :
    op223_nonsustainable_tree_fin_four_G1.Adj u v ↔
      (op223_nonsustainable_tree_fin_four_P4.Adj u v ∧ s(u, v) ≠ s(0, 1)) ∨ (s(u, v) = s(0, 3) ∧ u ≠ v) := by
  simp [op223_nonsustainable_tree_fin_four_G1, sup_adj, deleteEdges_adj, fromEdgeSet_adj]

lemma op223_nonsustainable_tree_fin_four_G2_adj (u v : Fin 4) :
    op223_nonsustainable_tree_fin_four_G2.Adj u v ↔
      (op223_nonsustainable_tree_fin_four_P4.Adj u v ∧ s(u, v) ≠ s(1, 2)) ∨ (s(u, v) = s(0, 2) ∧ u ≠ v) := by
  simp [op223_nonsustainable_tree_fin_four_G2, sup_adj, deleteEdges_adj, fromEdgeSet_adj]

lemma op223_nonsustainable_tree_fin_four_G3_adj (u v : Fin 4) :
    op223_nonsustainable_tree_fin_four_G3.Adj u v ↔
      (op223_nonsustainable_tree_fin_four_P4.Adj u v ∧ s(u, v) ≠ s(2, 3)) ∨ (s(u, v) = s(0, 3) ∧ u ≠ v) := by
  simp [op223_nonsustainable_tree_fin_four_G3, sup_adj, deleteEdges_adj, fromEdgeSet_adj]

def op223_nonsustainable_tree_fin_four_e1 : Fin 4 ≃ Fin 4 :=
  ⟨fun x => match x with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0,
   fun x => match x with | 1 => 0 | 2 => 1 | 3 => 2 | 0 => 3,
   by intro x; fin_cases x <;> rfl,
   by intro x; fin_cases x <;> rfl⟩

theorem op223_nonsustainable_tree_fin_four_G1_iso_P4 : ∀ u v : Fin 4,
    op223_nonsustainable_tree_fin_four_G1.Adj (op223_nonsustainable_tree_fin_four_e1 u)
      (op223_nonsustainable_tree_fin_four_e1 v) ↔ op223_nonsustainable_tree_fin_four_P4.Adj u v := by
  intro u v
  fin_cases u <;> fin_cases v <;>
    (simp only [op223_nonsustainable_tree_fin_four_e1, Equiv.coe_fn_mk,
      op223_nonsustainable_tree_fin_four_G1_adj, op223_nonsustainable_tree_fin_four_P4, pathGraph_adj]; decide)

def op223_nonsustainable_tree_fin_four_iso1 :
    op223_nonsustainable_tree_fin_four_P4 ≃g op223_nonsustainable_tree_fin_four_G1 where
  toEquiv := op223_nonsustainable_tree_fin_four_e1
  map_rel_iff' {u v} := op223_nonsustainable_tree_fin_four_G1_iso_P4 u v

def op223_nonsustainable_tree_fin_four_e2 : Fin 4 ≃ Fin 4 :=
  ⟨fun x => match x with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3,
   fun x => match x with | 1 => 0 | 0 => 1 | 2 => 2 | 3 => 3,
   by intro x; fin_cases x <;> rfl,
   by intro x; fin_cases x <;> rfl⟩

theorem op223_nonsustainable_tree_fin_four_G2_iso_P4 : ∀ u v : Fin 4,
    op223_nonsustainable_tree_fin_four_G2.Adj (op223_nonsustainable_tree_fin_four_e2 u)
      (op223_nonsustainable_tree_fin_four_e2 v) ↔ op223_nonsustainable_tree_fin_four_P4.Adj u v := by
  intro u v
  fin_cases u <;> fin_cases v <;>
    (simp only [op223_nonsustainable_tree_fin_four_e2, Equiv.coe_fn_mk,
      op223_nonsustainable_tree_fin_four_G2_adj, op223_nonsustainable_tree_fin_four_P4, pathGraph_adj]; decide)

def op223_nonsustainable_tree_fin_four_iso2 :
    op223_nonsustainable_tree_fin_four_P4 ≃g op223_nonsustainable_tree_fin_four_G2 where
  toEquiv := op223_nonsustainable_tree_fin_four_e2
  map_rel_iff' {u v} := op223_nonsustainable_tree_fin_four_G2_iso_P4 u v

def op223_nonsustainable_tree_fin_four_e3 : Fin 4 ≃ Fin 4 :=
  ⟨fun x => match x with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3,
   fun x => match x with | 2 => 0 | 1 => 1 | 0 => 2 | 3 => 3,
   by intro x; fin_cases x <;> rfl,
   by intro x; fin_cases x <;> rfl⟩

theorem op223_nonsustainable_tree_fin_four_G3_iso_P4 : ∀ u v : Fin 4,
    op223_nonsustainable_tree_fin_four_G3.Adj (op223_nonsustainable_tree_fin_four_e3 u)
      (op223_nonsustainable_tree_fin_four_e3 v) ↔ op223_nonsustainable_tree_fin_four_P4.Adj u v := by
  intro u v
  fin_cases u <;> fin_cases v <;>
    (simp only [op223_nonsustainable_tree_fin_four_e3, Equiv.coe_fn_mk,
      op223_nonsustainable_tree_fin_four_G3_adj, op223_nonsustainable_tree_fin_four_P4, pathGraph_adj]; decide)

def op223_nonsustainable_tree_fin_four_iso3 :
    op223_nonsustainable_tree_fin_four_P4 ≃g op223_nonsustainable_tree_fin_four_G3 where
  toEquiv := op223_nonsustainable_tree_fin_four_e3
  map_rel_iff' {u v} := op223_nonsustainable_tree_fin_four_G3_iso_P4 u v

lemma op223_nonsustainable_tree_fin_four_P4_edges (e : Sym2 (Fin 4))
    (he : e ∈ op223_nonsustainable_tree_fin_four_P4.edgeSet) :
    e = s(0, 1) ∨ e = s(1, 2) ∨ e = s(2, 3) := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgeSet, op223_nonsustainable_tree_fin_four_P4, pathGraph_adj] at he
    fin_cases u <;> fin_cases v <;> simp_all

lemma op223_nonsustainable_tree_fin_four_03_compl :
    s((0 : Fin 4), (3 : Fin 4)) ∈ op223_nonsustainable_tree_fin_four_P4ᶜ.edgeSet := by
  simp only [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj,
    op223_nonsustainable_tree_fin_four_P4, SimpleGraph.pathGraph_adj]
  decide

lemma op223_nonsustainable_tree_fin_four_02_compl :
    s((0 : Fin 4), (2 : Fin 4)) ∈ op223_nonsustainable_tree_fin_four_P4ᶜ.edgeSet := by
  simp only [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj,
    op223_nonsustainable_tree_fin_four_P4, SimpleGraph.pathGraph_adj]
  decide

theorem op223_nonsustainable_tree_fin_four_P4_sustainable
    (hP4_tree : op223_nonsustainable_tree_fin_four_P4.IsTree) :
    is_sustainable_tree op223_nonsustainable_tree_fin_four_P4 := by
  refine ⟨hP4_tree, ?_⟩
  intro e he
  rcases op223_nonsustainable_tree_fin_four_P4_edges e he with rfl | rfl | rfl
  · refine ⟨he, s(0, 3), op223_nonsustainable_tree_fin_four_03_compl,
      op223_nonsustainable_tree_fin_four_iso1.isTree_iff.mp hP4_tree, ?_⟩
    change adjacency_spectral_radius op223_nonsustainable_tree_fin_four_P4 ≤
      adjacency_spectral_radius op223_nonsustainable_tree_fin_four_G1
    rw [op223_nonsustainable_tree_fin_four_rad_iso op223_nonsustainable_tree_fin_four_iso1]
  · refine ⟨he, s(0, 2), op223_nonsustainable_tree_fin_four_02_compl,
      op223_nonsustainable_tree_fin_four_iso2.isTree_iff.mp hP4_tree, ?_⟩
    change adjacency_spectral_radius op223_nonsustainable_tree_fin_four_P4 ≤
      adjacency_spectral_radius op223_nonsustainable_tree_fin_four_G2
    rw [op223_nonsustainable_tree_fin_four_rad_iso op223_nonsustainable_tree_fin_four_iso2]
  · refine ⟨he, s(0, 3), op223_nonsustainable_tree_fin_four_03_compl,
      op223_nonsustainable_tree_fin_four_iso3.isTree_iff.mp hP4_tree, ?_⟩
    change adjacency_spectral_radius op223_nonsustainable_tree_fin_four_P4 ≤
      adjacency_spectral_radius op223_nonsustainable_tree_fin_four_G3
    rw [op223_nonsustainable_tree_fin_four_rad_iso op223_nonsustainable_tree_fin_four_iso3]

/-- Every non-sustainable tree on 4 vertices is isomorphic to the star completeBipartiteGraph (Fin 1) (Fin 3). -/
theorem op223_nonsustainable_tree_fin_four (X : SimpleGraph (Fin 4))
    (hX : is_nonsustainable_tree X) :
    Nonempty (X ≃g completeBipartiteGraph (Fin 1) (Fin 3)) := by
  rcases op223_tree_fin_four_iso_path_or_star X hX.1 with ⟨⟨iso_path⟩⟩ | hstar
  · exfalso
    have htree_P4 : op223_nonsustainable_tree_fin_four_P4.IsTree := iso_path.isTree_iff.mp hX.1
    have hsust_P4 : is_sustainable_tree op223_nonsustainable_tree_fin_four_P4 :=
      op223_nonsustainable_tree_fin_four_P4_sustainable htree_P4
    have hsust_X : is_sustainable_tree X :=
      op223_nonsustainable_tree_fin_four_is_sustainable_tree_iso iso_path.symm hsust_P4
    exact hX.2 hsust_X
  · exact hstar
