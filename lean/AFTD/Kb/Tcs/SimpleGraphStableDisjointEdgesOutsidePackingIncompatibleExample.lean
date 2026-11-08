import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumberMono
import AFTD.Kb.Tcs.G

/-!
# simple_graph_stable_disjoint_edges_outside_packing_incompatible_example

Topic: graphs   Node: 3daee0f87a72

Provenance: helper lemma. Explicit seven-vertex computation, experiments 16021 and 16025; triangle packing definition from arXiv:2610.15539, Section 1.

There is a stable graph of triangle packing number three, a maximum packing P, and a five-edge triangle cover containing two vertex-disjoint edges outside P that do not both occur in any maximum packing.
-/

open scoped Sym2

/-- The fourteen edges of the seven-vertex witness graph. -/
def simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_E :
    Finset (Sym2 (Fin 7)) :=
  {s(0,3), s(0,4), s(0,6), s(1,2), s(1,4), s(1,5), s(2,3), s(2,5), s(2,6), s(3,5), s(3,6),
    s(4,5), s(4,6), s(5,6)}

/-- The seven-vertex witness graph with fourteen edges. -/
def simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_G :
    SimpleGraph (Fin 7) where
  Adj u v := s(u,v) ∈ simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_E ∧ u ≠ v
  symm := Std.Symm.mk (fun u v h => ⟨by rw [Sym2.eq_swap]; exact h.1, h.2.symm⟩)
  loopless := Std.Irrefl.mk (fun u h => h.2 rfl)

/-- Decidability of adjacency in the witness graph. -/
instance simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_decidableRel :
    DecidableRel simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_G.Adj :=
  fun u v => decidable_of_decidable_of_iff
    (p := s(u,v) ∈ simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_E ∧ u ≠ v)
    (q := simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_G.Adj u v) Iff.rfl

/-- The nine triangles of the seven-vertex witness graph. -/
def simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangles :
    Finset (Finset (Fin 7)) :=
  {{0,3,6},{0,4,6},{1,2,5},{1,4,5},{2,3,5},{2,3,6},{2,5,6},{3,5,6},{4,5,6}}

/-- The displayed five-edge triangle cover. -/
def simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_cover :
    Finset (Sym2 (Fin 7)) := {s(0,3), s(1,5), s(2,6), s(3,5), s(4,6)}

/-- Every three-clique of the witness graph is one of the nine listed triangles. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangle_check :
    ∀ t ∈ (Finset.univ : Finset (Fin 7)).powersetCard 3,
      simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_G.IsNClique 3 t →
      t ∈ simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangles := by
  decide

/-- No four of the nine triangles of the witness graph are pairwise edge-disjoint. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_no_four_disjoint :
    ((simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangles.powersetCard 4).filter
      (fun Q => ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → (x ∩ y).card ≤ 1)) = ∅ := by
  decide

/-- The triangles of the witness graph through the edge `{2,6}` are the stated two. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_contains_26 :
    ∀ t ∈ simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangles,
      (2 : Fin 7) ∈ t → (6 : Fin 7) ∈ t →
      t ∈ ({{2,3,6},{2,5,6}} : Finset (Finset (Fin 7))) := by
  decide

/-- The triangles of the witness graph through the edge `{3,5}` are the stated two. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_contains_35 :
    ∀ t ∈ simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangles,
      (3 : Fin 7) ∈ t → (5 : Fin 7) ∈ t →
      t ∈ ({{2,3,5},{3,5,6}} : Finset (Finset (Fin 7))) := by
  decide

/-- No triangle through `{2,6}` is edge-disjoint from a triangle through `{3,5}`. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_incompatible_pairs :
    ∀ u ∈ ({{2,3,6},{2,5,6}} : Finset (Finset (Fin 7))),
      ∀ w ∈ ({{2,3,5},{3,5,6}} : Finset (Finset (Fin 7))), u ≠ w ∧ 1 < (u ∩ w).card := by
  decide

/-- Membership in the non-diagonal edge encoding of a finite vertex set. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_mem_encoding
    {t : Finset (Fin 7)} {a b : Fin 7} :
    s(a,b) ∈ finite_vertex_set_edge_encoding t ↔ a ∈ t ∧ b ∈ t ∧ a ≠ b := by
  simp [finite_vertex_set_edge_encoding, Sym2.mk_isDiag_iff, and_assoc]

/-- A family of pairwise edge-disjoint triangles has at most `ν` members. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_card_le_packing_number
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (T : Finset (Finset V))
    (hc : ∀ t ∈ T, H.IsNClique 3 t)
    (hpw : (T : Set (Finset V)).Pairwise fun a b => (a ∩ b).card ≤ 1) :
    T.card ≤ simple_graph_triangle_packing_number H := by
  rw [simple_graph_triangle_packing_number.eq_1]
  refine le_csSup ?_ ⟨T, hc, hpw, rfl⟩
  refine ⟨(Finset.univ : Finset (Finset V)).card, ?_⟩
  rintro n ⟨T', -, -, hcard⟩
  rw [← hcard]
  exact Finset.card_le_card (Finset.subset_univ T')

/-- Every edge of the witness graph belongs to the displayed fourteen edges. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_mem_edge_set_of_mem :
    ∀ g : Sym2 (Fin 7),
      g ∈ simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_G.edgeSet →
      g ∈ simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_E := by
  intro g
  induction g using Sym2.ind with
  | _ a b =>
    intro h
    rw [SimpleGraph.mem_edgeSet] at h
    exact h.1

/-- Every three-clique of the witness graph lies in the displayed triangle list. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangle_mem
    (t : Finset (Fin 7))
    (ht : simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_G.IsNClique 3 t) :
    t ∈ simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangles := by
  refine simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangle_check
    t ?_ ht
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ t, ((SimpleGraph.isNClique_iff _).mp ht).2⟩

/-- Every family of pairwise edge-disjoint triangles of the witness graph has at most three members. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_card_le_three
    (T : Finset (Finset (Fin 7)))
    (hcl : ∀ t ∈ T, simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_G.IsNClique 3 t)
    (hpw : (T : Set (Finset (Fin 7))).Pairwise fun a b => (a ∩ b).card ≤ 1) : T.card ≤ 3 := by
  by_contra hle
  have hge : 4 ≤ T.card := by omega
  obtain ⟨Q, hQT, hQc⟩ := Finset.exists_subset_card_eq hge
  have hQA : Q ⊆ simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangles :=
    fun t ht => simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangle_mem
      t (hcl t (hQT ht))
  have hQpw : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → (x ∩ y).card ≤ 1 :=
    fun x hx y hy hne => hpw (hQT hx) (hQT hy) hne
  have hmem :
      Q ∈ simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangles.powersetCard 4 :=
    (Finset.mem_powersetCard).mpr ⟨hQA, hQc⟩
  have hfil : Q ∈ ((simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangles.powersetCard 4).filter
      (fun Q => ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → (x ∩ y).card ≤ 1)) :=
    (Finset.mem_filter).mpr ⟨hmem, hQpw⟩
  rw [simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_no_four_disjoint] at hfil
  exact Finset.notMem_empty Q hfil

/-- The witness graph has triangle packing number at most three. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_packing_number_le_three :
    simple_graph_triangle_packing_number
      simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_G ≤ 3 := by
  rw [simple_graph_triangle_packing_number.eq_1]
  refine csSup_le ⟨0, ∅, by simp, by simp, rfl⟩ ?_
  rintro n ⟨T, h1, h2, h3⟩
  rw [← h3]
  exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_card_le_three T h1 h2

/-- Three pairwise edge-disjoint triangles force the packing number to be at least three. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing
    (H : SimpleGraph (Fin 7)) (T : Finset (Finset (Fin 7)))
    (hcl : ∀ t ∈ T, H.IsNClique 3 t)
    (hpw : (T : Set (Finset (Fin 7))).Pairwise fun a b => (a ∩ b).card ≤ 1)
    (hc : T.card = 3) : 3 ≤ simple_graph_triangle_packing_number H := by
  rw [← hc]
  exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_card_le_packing_number
    H T hcl hpw

/-- The witness graph has triangle packing number exactly three. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_packing_number_eq_three :
    simple_graph_triangle_packing_number
      simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_G = 3 := by
  refine le_antisymm
    simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_packing_number_le_three ?_
  exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing
    _ {{0,3,6},{4,5,6},{1,2,5}} (by decide) (by decide) (by decide)

/-- Deleting any edge of the witness graph preserves its triangle packing number. -/
theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_delete_packing_number :
    ∀ g ∈ simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_G.edgeSet,
      simple_graph_triangle_packing_number
          (simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_G.deleteEdges {g}) =
        simple_graph_triangle_packing_number
          simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_G := by
  intro g hg
  have hgE : g ∈ simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_E :=
    simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_mem_edge_set_of_mem g hg
  rw [simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_packing_number_eq_three]
  refine le_antisymm ?_ ?_
  · exact le_trans (simple_graph_triangle_packing_number_mono _ _
      (SimpleGraph.deleteEdges_le {g})) (le_of_eq
        simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_packing_number_eq_three)
  · have hcases : g = s(0,3) ∨ g = s(0,4) ∨ g = s(0,6) ∨ g = s(1,2) ∨ g = s(1,4) ∨
        g = s(1,5) ∨ g = s(2,3) ∨ g = s(2,5) ∨ g = s(2,6) ∨ g = s(3,5) ∨ g = s(3,6) ∨
        g = s(4,5) ∨ g = s(4,6) ∨ g = s(5,6) := by
      simpa [simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_E] using hgE
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{1,2,5},{2,3,6},{4,5,6}} (by decide) (by decide) (by decide)
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{1,2,5},{2,3,6},{4,5,6}} (by decide) (by decide) (by decide)
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{1,2,5},{2,3,6},{4,5,6}} (by decide) (by decide) (by decide)
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{0,4,6},{1,4,5},{3,5,6}} (by decide) (by decide) (by decide)
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{1,2,5},{2,3,6},{4,5,6}} (by decide) (by decide) (by decide)
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{0,3,6},{2,3,5},{4,5,6}} (by decide) (by decide) (by decide)
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{0,4,6},{1,4,5},{3,5,6}} (by decide) (by decide) (by decide)
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{0,4,6},{1,4,5},{3,5,6}} (by decide) (by decide) (by decide)
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{0,4,6},{1,4,5},{3,5,6}} (by decide) (by decide) (by decide)
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{1,2,5},{2,3,6},{4,5,6}} (by decide) (by decide) (by decide)
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{0,4,6},{1,4,5},{2,5,6}} (by decide) (by decide) (by decide)
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{0,4,6},{1,2,5},{3,5,6}} (by decide) (by decide) (by decide)
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{0,3,6},{1,4,5},{2,5,6}} (by decide) (by decide) (by decide)
    · exact simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_three_le_of_packing _ {{0,4,6},{1,4,5},{2,3,6}} (by decide) (by decide) (by decide)

theorem simple_graph_stable_disjoint_edges_outside_packing_incompatible_example :
    ∃ (G : SimpleGraph (Fin 7)) (P : Finset (Finset (Fin 7)))
      (C : Finset (Sym2 (Fin 7))) (e f : Sym2 (Fin 7)),
      simple_graph_triangle_packing_number G = 3 ∧
      (∀ g ∈ G.edgeSet,
        simple_graph_triangle_packing_number (G.deleteEdges {g}) =
          simple_graph_triangle_packing_number G) ∧
      (∀ t ∈ P, G.IsNClique 3 t) ∧
      (P : Set (Finset (Fin 7))).Pairwise (fun a b => (a ∩ b).card ≤ 1) ∧
      P.card = simple_graph_triangle_packing_number G ∧
      (∀ g ∈ C, g ∈ G.edgeSet) ∧
      (∀ t : Finset (Fin 7), G.IsNClique 3 t → ∃ g ∈ C, ∀ x ∈ g, x ∈ t) ∧
      C.card = 5 ∧ e ∈ C ∧ f ∈ C ∧ (∀ x ∈ e, x ∉ f) ∧
      e ∉ (P.image finite_vertex_set_edge_encoding).biUnion id ∧
      f ∉ (P.image finite_vertex_set_edge_encoding).biUnion id ∧
      ∀ Q : Finset (Finset (Fin 7)),
        (∀ t ∈ Q, G.IsNClique 3 t) →
        (Q : Set (Finset (Fin 7))).Pairwise (fun a b => (a ∩ b).card ≤ 1) →
        Q.card = simple_graph_triangle_packing_number G →
        ¬ (e ∈ (Q.image finite_vertex_set_edge_encoding).biUnion id ∧
           f ∈ (Q.image finite_vertex_set_edge_encoding).biUnion id) := by
  refine ⟨simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_G,
    {{0,3,6},{4,5,6},{1,2,5}},
    simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_cover,
    s(2,6), s(3,5),
    simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_packing_number_eq_three,
    simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_delete_packing_number,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · rw [simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_packing_number_eq_three]
    decide
  · intro g hg
    simp only [simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_cover,
      Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    all_goals (rw [SimpleGraph.mem_edgeSet]; decide)
  · intro t ht
    have hA := simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangle_mem t ht
    simp only [simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangles,
      Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro Q hQcl hQpw hQcard hin
    obtain ⟨hin26, hin35⟩ := hin
    obtain ⟨u, huQ, heu⟩ := Finset.mem_biUnion.mp hin26
    obtain ⟨t, htQ, rfl⟩ := Finset.mem_image.mp huQ
    obtain ⟨u', hu'Q, hfu'⟩ := Finset.mem_biUnion.mp hin35
    obtain ⟨t', ht'Q, rfl⟩ := Finset.mem_image.mp hu'Q
    obtain ⟨h2t, h6t, -⟩ :=
      simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_mem_encoding.mp heu
    obtain ⟨h3t, h5t, -⟩ :=
      simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_mem_encoding.mp hfu'
    have hS1 := simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_contains_26 t
      (simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangle_mem t
        (hQcl t htQ)) h2t h6t
    have hS2 := simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_contains_35 t'
      (simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_triangle_mem t'
        (hQcl t' ht'Q)) h3t h5t
    obtain ⟨hne, hgt⟩ :=
      simple_graph_stable_disjoint_edges_outside_packing_incompatible_example_incompatible_pairs
        t hS1 t' hS2
    exact absurd (hQpw htQ ht'Q hne) (by omega)
