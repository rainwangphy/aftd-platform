import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIn693TenSeedPackingNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_maximum_packing_fixed_two_budget_counterexample

Topic: graphs   Node: 1c7b4a4e19a0

Provenance: helper lemma. Three four-cliques in a vertex cycle, extracted in experiments 20948 and 20962; see state/campaigns/triangle_reductions/k4_pivot_cover_in701.md. Related forced-triangle and packing-cover structure is in https://arxiv.org/abs/2001.00257, Section 3. Literature checked 2026-11-10.

A nine-vertex graph has a maximum triangle packing with at most one singleton-forced edge per packed triangle, but no triangle cover formed by choosing exactly two edges from each packed triangle. It nevertheless has a six-edge cover supported by that packing.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
namespace In701Budget
def EL : List (Sym2 (Fin 9)) := [s(0,1), s(0,2), s(0,3), s(1,2), s(1,3), s(2,3), s(2,5), s(2,7), s(2,8), s(3,4), s(3,5), s(3,6), s(4,5), s(4,6), s(5,6), s(5,7), s(5,8), s(7,8)]
def T : List (Finset (Fin 9)) := [{0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}, {2,3,5}, {2,5,7}, {2,5,8}, {2,7,8}, {3,4,5}, {3,4,6}, {3,5,6}, {4,5,6}, {5,7,8}]
def P : Finset (Finset (Fin 9)) := {{0,1,2}, {3,4,6}, {2,3,5}, {2,7,8}}
def E : Finset (Sym2 (Fin 9)) := EL.toFinset
def G : SimpleGraph (Fin 9) where
  Adj u v := s(u,v) ∈ E ∧ u ≠ v
  symm := ⟨fun u v h => ⟨by rw [Sym2.eq_swap]; exact h.1, h.2.symm⟩⟩
  loopless := ⟨fun u h => h.2 rfl⟩
instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ E ∧ _ ≠ _))
def PI : Fin 4 → Finset (Fin 9) := ![{0,1,2}, {3,4,6}, {2,3,5}, {2,7,8}]
def Choice : Fin 4 → Fin 3 → Finset (Sym2 (Fin 9)) := ![![{s(0,1), s(0,2)}, {s(0,1), s(1,2)}, {s(0,2), s(1,2)}], ![{s(3,4), s(3,6)}, {s(3,4), s(4,6)}, {s(3,6), s(4,6)}], ![{s(2,3), s(2,5)}, {s(2,3), s(3,5)}, {s(2,5), s(3,5)}], ![{s(2,7), s(2,8)}, {s(2,7), s(7,8)}, {s(2,8), s(7,8)}]]
def SmallCover : Finset (Sym2 (Fin 9)) := {s(0,1), s(2,3), s(2,5), s(3,5), s(4,6), s(7,8)}
def Picks (f : Fin 4 → Fin 3) : Finset (Sym2 (Fin 9)) :=
  (Finset.univ : Finset (Fin 4)).biUnion (fun i => Choice i (f i))

theorem tri_complete : ∀ t ∈ (Finset.univ : Finset (Fin 9)).powersetCard 3,
    G.IsNClique 3 t → t ∈ T := by decide +kernel
theorem T_clique : ∀ t ∈ T, G.IsNClique 3 t := by decide +kernel
lemma clique_mem {t : Finset (Fin 9)} (h : G.IsNClique 3 t) : t ∈ T :=
  tri_complete t (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h.card_eq⟩) h
def compat (s t : Finset (Fin 9)) : Bool := decide ((s ∩ t).card ≤ 1)
theorem maxC_eq : in693_maxC compat T.length T = 4 := by decide +kernel
lemma nu_le (U : Finset (Finset (Fin 9))) (hU : ∀ t ∈ U, G.IsNClique 3 t)
    (hP : (U : Set (Finset (Fin 9))).Pairwise (fun a b => (a ∩ b).card ≤ 1)) : U.card ≤ 4 :=
  calc U.card ≤ in693_maxC compat T.length T :=
        in693_maxC_bound compat _ T le_rfl U (fun a ha => clique_mem (hU a ha))
          (fun a ha b hb hab => decide_eq_true (hP (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab))
    _ = 4 := maxC_eq

theorem P_clique : ∀ t ∈ P, G.IsNClique 3 t := by decide +kernel
theorem P_pw : (P : Set (Finset (Fin 9))).Pairwise (fun a b => (a ∩ b).card ≤ 1) := by decide +kernel
theorem P_card : P.card = 4 := by decide +kernel
theorem pack_eq : simple_graph_triangle_packing_number G = 4 := by
  unfold simple_graph_triangle_packing_number
  refine IsGreatest.csSup_eq ⟨⟨P, P_clique, P_pw, P_card⟩, ?_⟩
  rintro n ⟨U, h1, h2, rfl⟩
  exact nu_le U h1 h2

theorem family : simple_graph_triangle_edge_family G =
    T.toFinset.image finite_vertex_set_edge_encoding := by
  classical
  ext x
  simp only [simple_graph_triangle_edge_family, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, clique_mem ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, T_clique t ht, rfl⟩

theorem forced_le : ∀ p ∈ P, (finite_vertex_set_edge_encoding p ∩
   (((simple_graph_triangle_edge_family G).filter
     (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id)).card ≤ 1 := by
  rw [family]
  decide +kernel

theorem choices_ok : (∀ i : Fin 4, PI i ∈ P) ∧ Function.Injective PI ∧
    (∀ i : Fin 4, ∀ j : Fin 3, (Choice i j).card = 2 ∧ Choice i j ⊆ finite_vertex_set_edge_encoding (PI i)) ∧
    (∀ i : Fin 4, Function.Injective (Choice i)) := by decide +kernel

theorem no_selection : ∀ f : Fin 4 → Fin 3, ∃ t ∈ T,
    Disjoint (finite_vertex_set_edge_encoding t) (Picks f) := by decide +kernel

theorem small_cover : SmallCover.card = 6 ∧ SmallCover ⊆ P.biUnion finite_vertex_set_edge_encoding ∧
    ∀ t ∈ T, ¬ Disjoint (finite_vertex_set_edge_encoding t) SmallCover := by decide +kernel
end In701Budget

theorem simple_graph_maximum_packing_fixed_two_budget_counterexample :
    (∀ t ∈ In701Budget.P, In701Budget.G.IsNClique 3 t) ∧
    (In701Budget.P : Set (Finset (Fin 9))).Pairwise (fun a b => (a ∩ b).card ≤ 1) ∧
    In701Budget.P.card = simple_graph_triangle_packing_number In701Budget.G ∧
    (∀ p ∈ In701Budget.P, (finite_vertex_set_edge_encoding p ∩
      (((simple_graph_triangle_edge_family In701Budget.G).filter
        (fun t => (t ∩ In701Budget.P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id)).card ≤ 1) ∧
    (∀ i : Fin 4, In701Budget.PI i ∈ In701Budget.P) ∧ Function.Injective In701Budget.PI ∧
    (∀ i : Fin 4, ∀ j : Fin 3, (In701Budget.Choice i j).card = 2 ∧ In701Budget.Choice i j ⊆ finite_vertex_set_edge_encoding (In701Budget.PI i)) ∧
    (∀ i : Fin 4, Function.Injective (In701Budget.Choice i)) ∧
    (∀ f : Fin 4 → Fin 3, ∃ t : Finset (Fin 9), In701Budget.G.IsNClique 3 t ∧
      Disjoint (finite_vertex_set_edge_encoding t) (In701Budget.Picks f)) ∧
    (In701Budget.SmallCover.card = 6 ∧ In701Budget.SmallCover ⊆ In701Budget.P.biUnion finite_vertex_set_edge_encoding ∧
      ∀ t : Finset (Fin 9), In701Budget.G.IsNClique 3 t → ¬ Disjoint (finite_vertex_set_edge_encoding t) In701Budget.SmallCover) := by
  refine ⟨In701Budget.P_clique,In701Budget.P_pw,?_,In701Budget.forced_le,In701Budget.choices_ok.1,In701Budget.choices_ok.2.1,In701Budget.choices_ok.2.2.1,In701Budget.choices_ok.2.2.2,?_,?_⟩
  · rw [In701Budget.P_card,In701Budget.pack_eq]
  · intro f
    obtain ⟨t,ht,hd⟩ := In701Budget.no_selection f
    exact ⟨t,In701Budget.T_clique t ht,hd⟩
  · refine ⟨In701Budget.small_cover.1,In701Budget.small_cover.2.1,?_⟩
    intro t ht
    exact In701Budget.small_cover.2.2 t (In701Budget.clique_mem ht)
