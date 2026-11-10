import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIn693TenSeedPackingNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_pair_stable_triangle_active_incidence_two_unpacked_nonbipartite

Topic: graphs   Node: fa68d411a121

Provenance: helper lemma. The explicit finite counterexample in state/campaigns/triangle_reductions/incidence_two_nonbipartite_cert_in701.json refutes an unpacked-edge bipartiteness shortcut, even when every edge belongs to a triangle.

There is a triangle-active two-edge-stable eight-vertex graph with a support-maximal maximum triangle packing in which every vertex is in at most two packed triangles, while the graph of unpacked edges is not bipartite.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
namespace In701Free

def EL : List (Sym2 (Fin 8)) := [s(0,2), s(0,4), s(0,6), s(0,7), s(1,3), s(1,5), s(1,6), s(1,7), s(2,4), s(2,6), s(2,7), s(3,5), s(3,6), s(3,7), s(4,6), s(4,7), s(5,6), s(5,7), s(6,7)]
def T : List (Finset (Fin 8)) := [{0,2,4}, {0,2,6}, {0,2,7}, {0,4,6}, {0,4,7}, {0,6,7}, {1,3,5}, {1,3,6}, {1,3,7}, {1,5,6}, {1,5,7}, {1,6,7}, {2,4,6}, {2,4,7}, {2,6,7}, {3,5,6}, {3,5,7}, {3,6,7}, {4,6,7}, {5,6,7}]
def P : Finset (Finset (Fin 8)) := {{0,2,4}, {0,6,7}, {1,3,6}, {3,5,7}}
def E : Finset (Sym2 (Fin 8)) := EL.toFinset
def G : SimpleGraph (Fin 8) where
  Adj u v := s(u,v) ∈ E ∧ u ≠ v
  symm := ⟨fun u v h => ⟨by rw [Sym2.eq_swap]; exact h.1, h.2.symm⟩⟩
  loopless := ⟨fun u h => h.2 rfl⟩
instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ E ∧ _ ≠ _))

theorem tri_complete : ∀ t ∈ (Finset.univ : Finset (Fin 8)).powersetCard 3,
    G.IsNClique 3 t → t ∈ T := by decide +kernel
theorem T_clique : ∀ t ∈ T, G.IsNClique 3 t := by decide +kernel
lemma clique_mem {t : Finset (Fin 8)} (h : G.IsNClique 3 t) : t ∈ T :=
  tri_complete t (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h.card_eq⟩) h
def compat (s t : Finset (Fin 8)) : Bool := decide ((s ∩ t).card ≤ 1)
theorem maxC_eq : in693_maxC compat T.length T = 4 := by decide +kernel
lemma nu_le (U : Finset (Finset (Fin 8))) (hU : ∀ t ∈ U, G.IsNClique 3 t)
    (hP : (U : Set (Finset (Fin 8))).Pairwise (fun a b => (a ∩ b).card ≤ 1)) : U.card ≤ 4 :=
  calc U.card ≤ in693_maxC compat T.length T :=
        in693_maxC_bound compat _ T le_rfl U (fun a ha => clique_mem (hU a ha))
          (fun a ha b hb hab => decide_eq_true (hP (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab))
    _ = 4 := maxC_eq

theorem P_clique : ∀ t ∈ P, G.IsNClique 3 t := by decide +kernel
theorem P_pw : (P : Set (Finset (Fin 8))).Pairwise (fun a b => (a ∩ b).card ≤ 1) := by decide +kernel
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
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, clique_mem ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, T_clique t ht, rfl⟩

theorem P_support : P.biUnion id = Finset.univ := by decide +kernel
theorem P_mult : ∀ v : Fin 8, (P.filter (fun t => v ∈ t)).card ≤ 2 := by decide +kernel
theorem P_nonbip : ∀ f : Fin 8 → Bool, ∃ u v : Fin 8,
    G.Adj u v ∧ s(u,v) ∉ P.biUnion finite_vertex_set_edge_encoding ∧ f u = f v := by decide +kernel

theorem T_active : ∀ e ∈ EL, ∃ t ∈ T, e ∈ finite_vertex_set_edge_encoding t := by decide +kernel

def W : List (List (Sym2 (Fin 8)) × List (Finset (Fin 8))) := [
  ([s(0,2), s(0,4), s(1,3), s(1,6), s(2,6), s(3,7), s(4,6)], [{0,6,7}, {1,5,7}, {2,4,7}, {3,5,6}]),
  ([s(0,2), s(0,6), s(2,7), s(3,5), s(3,6), s(5,7), s(6,7)], [{0,4,7}, {1,3,7}, {1,5,6}, {2,4,6}]),
  ([s(0,2), s(0,7), s(1,5), s(1,7), s(2,4), s(4,7), s(5,6)], [{0,4,6}, {1,3,6}, {2,6,7}, {3,5,7}]),
  ([s(0,4), s(0,6), s(1,3), s(1,5), s(3,6), s(4,7), s(5,6)], [{0,2,7}, {1,6,7}, {2,4,6}, {3,5,7}]),
  ([s(1,5), s(1,6), s(2,4), s(2,6), s(4,7), s(5,7), s(6,7)], [{0,2,7}, {0,4,6}, {1,3,7}, {3,5,6}]),
  ([s(0,4), s(0,7), s(1,3), s(1,7), s(3,5), s(4,6), s(5,7)], [{0,2,6}, {1,5,6}, {2,4,7}, {3,6,7}]),
  ([s(2,4), s(2,7), s(3,5), s(3,7), s(4,6), s(5,6), s(6,7)], [{0,2,6}, {0,4,7}, {1,3,6}, {1,5,7}]),
  ([s(0,6), s(0,7), s(1,3), s(1,7), s(2,6), s(2,7), s(3,6)], [{0,2,4}, {1,5,6}, {3,5,7}, {4,6,7}]),
  ([s(1,5), s(1,6), s(2,4), s(2,7), s(3,5), s(3,6), s(4,6)], [{0,2,6}, {0,4,7}, {1,3,7}, {5,6,7}]),
  ([s(0,6), s(0,7), s(1,3), s(1,6), s(3,7), s(4,6), s(4,7)], [{0,2,4}, {1,5,7}, {2,6,7}, {3,5,6}]),
  ([s(1,3), s(1,6), s(2,4), s(2,6), s(3,5), s(4,7), s(5,6)], [{0,2,7}, {0,4,6}, {1,5,7}, {3,6,7}]),
  ([s(0,4), s(0,7), s(1,3), s(1,7), s(3,6), s(4,6), s(6,7)], [{0,2,6}, {1,5,6}, {2,4,7}, {3,5,7}]),
  ([s(0,2), s(0,6), s(1,6), s(1,7), s(2,7), s(3,6), s(3,7)], [{0,4,7}, {1,3,5}, {2,4,6}, {5,6,7}]),
  ([s(0,2), s(0,4), s(1,3), s(1,6), s(2,7), s(3,7), s(4,7)], [{0,6,7}, {1,5,7}, {2,4,6}, {3,5,6}]),
  ([s(0,2), s(0,6), s(1,3), s(1,5), s(2,7), s(3,7), s(5,7)], [{0,4,7}, {1,6,7}, {2,4,6}, {3,5,6}]),
  ([s(0,4), s(0,6), s(1,3), s(1,6), s(2,4), s(2,6), s(3,7)], [{0,2,7}, {1,5,7}, {3,5,6}, {4,6,7}]),
  ([s(0,2), s(0,6), s(1,6), s(1,7), s(2,7), s(5,6), s(5,7)], [{0,4,7}, {1,3,5}, {2,4,6}, {3,6,7}])
]
theorem W_cover : ∀ e ∈ EL, ∀ f ∈ EL,
    ∃ q ∈ W, e ∈ q.1 ∧ f ∈ q.1 := by decide +kernel

theorem W_ok : ∀ q ∈ W, q.2.toFinset.card = 4 ∧
    (∀ t ∈ q.2, t ∈ T) ∧
    (∀ a ∈ q.2, ∀ b ∈ q.2, a ≠ b → (a ∩ b).card ≤ 1) ∧
    (∀ e ∈ q.1, ∀ t ∈ q.2, e ∉ t.sym2) := by decide +kernel

lemma edge_mem {g : Sym2 (Fin 8)} (h : g ∈ G.edgeSet) : g ∈ EL := by
  induction g using Sym2.ind with
  | _ a b =>
    have h1 := ((SimpleGraph.mem_edgeSet G).mp h).1
    exact List.mem_toFinset.mp h1

theorem active : ∀ e : Sym2 (Fin 8), e ∈ G.edgeSet →
    ∃ t : Finset (Fin 8), G.IsNClique 3 t ∧ e ∈ finite_vertex_set_edge_encoding t := by
  intro e he
  obtain ⟨t,ht,het⟩ := T_active e (edge_mem he)
  exact ⟨t,T_clique t ht,het⟩

lemma del_clique {t : Finset (Fin 8)} {e f : Sym2 (Fin 8)}
    (h : G.IsNClique 3 t) (he : ¬ ∀ x ∈ e, x ∈ t) (hf : ¬ ∀ x ∈ f, x ∈ t) :
    (G.deleteEdges {e,f}).IsNClique 3 t := by
  refine ⟨?_, h.card_eq⟩
  intro a ha b hb hab
  refine (SimpleGraph.deleteEdges_adj).mpr ⟨h.isClique ha hb hab, ?_⟩
  intro hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · apply he
    rw [← hmem]
    intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption
  · apply hf
    rw [← hmem]
    intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption

theorem stable : ∀ e f : Sym2 (Fin 8), e ∈ G.edgeSet → f ∈ G.edgeSet →
    e ≠ f → simple_graph_triangle_packing_number (G.deleteEdges {e,f}) =
      simple_graph_triangle_packing_number G := by
  intro e f he hf hne
  rw [pack_eq]
  obtain ⟨q, hq, hqe, hqf⟩ := W_cover e (edge_mem he) f (edge_mem hf)
  obtain ⟨hc, ht, hp, hav⟩ := W_ok q hq
  unfold simple_graph_triangle_packing_number
  refine IsGreatest.csSup_eq ⟨⟨q.2.toFinset, ?_, ?_, hc⟩, ?_⟩
  · intro t ht'
    have ht'' := List.mem_toFinset.mp ht'
    apply del_clique (T_clique t (ht t ht''))
    · intro h; exact hav e hqe t ht'' (Finset.mem_sym2_iff.mpr h)
    · intro h; exact hav f hqf t ht'' (Finset.mem_sym2_iff.mpr h)
  · intro a ha b hb hab
    exact hp a (List.mem_toFinset.mp (Finset.mem_coe.mp ha))
      b (List.mem_toFinset.mp (Finset.mem_coe.mp hb)) hab
  · rintro k ⟨U, hU, hP, rfl⟩
    exact nu_le U (fun t ht' => (hU t ht').mono (SimpleGraph.deleteEdges_le _)) hP
end In701Free

theorem simple_graph_pair_stable_triangle_active_incidence_two_unpacked_nonbipartite : ∃ (G : SimpleGraph (Fin 8)) (P : Finset (Finset (Fin 8))),
    (∀ t ∈ P, G.IsNClique 3 t) ∧
    (P : Set (Finset (Fin 8))).Pairwise (fun t u => (t ∩ u).card ≤ 1) ∧
    P.card = simple_graph_triangle_packing_number G ∧ P.biUnion id = Finset.univ ∧
    (∀ v : Fin 8, (P.filter (fun t => v ∈ t)).card ≤ 2) ∧
    (∀ e f : Sym2 (Fin 8), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
       simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G) ∧
    (∀ e : Sym2 (Fin 8), e ∈ G.edgeSet → ∃ t : Finset (Fin 8), G.IsNClique 3 t ∧ e ∈ finite_vertex_set_edge_encoding t) ∧
    (∀ f : Fin 8 → Bool, ∃ u v : Fin 8, G.Adj u v ∧
      s(u,v) ∉ P.biUnion finite_vertex_set_edge_encoding ∧ f u = f v) := by
  refine ⟨In701Free.G,In701Free.P,In701Free.P_clique,In701Free.P_pw,?_,In701Free.P_support,In701Free.P_mult,In701Free.stable,In701Free.active,In701Free.P_nonbip⟩
  rw [In701Free.P_card,In701Free.pack_eq]
