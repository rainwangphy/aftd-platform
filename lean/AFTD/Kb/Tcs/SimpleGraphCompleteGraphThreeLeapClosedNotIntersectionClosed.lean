import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsLeapClosed
import AFTD.Kb.Tcs.SimpleGraphLeapGroup
import AFTD.Kb.Tcs.SimpleGraphIsHopMemLeapGroup
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_completeGraph_three_leap_closed_not_intersection_closed

Topic: graphs   Node: 1254aabec1a6

Provenance: helper lemma. arXiv:2610.18463 Question 5.9

The collection of leap-closed edge subsets of the complete graph K₃ on 3 vertices is not closed under intersection.
-/

open scoped Sym2

/-- In the path 1–0–2, vertex 1 has only neighbour 0. -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_mem_path_a
    (x : Fin 3) (hx : s(1, x) ∈ ({s(0,1), s(0,2)} : Set (Sym2 (Fin 3)))) : x = 0 := by
  fin_cases x <;> simp_all

/-- In the path 1–0–2, vertex 2 has only neighbour 0. -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_mem_path_b
    (x : Fin 3) (hx : s(2, x) ∈ ({s(0,1), s(0,2)} : Set (Sym2 (Fin 3)))) : x = 0 := by
  fin_cases x <;> simp_all

/-- In the path 0–1–2, vertex 0 has only neighbour 1. -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_mem_path_c
    (x : Fin 3) (hx : s(0, x) ∈ ({s(0,1), s(1,2)} : Set (Sym2 (Fin 3)))) : x = 1 := by
  fin_cases x <;> simp_all

/-- In the path 0–1–2, vertex 2 has only neighbour 1. -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_mem_path_d
    (x : Fin 3) (hx : s(2, x) ∈ ({s(0,1), s(1,2)} : Set (Sym2 (Fin 3)))) : x = 1 := by
  fin_cases x <;> simp_all

/-- In the single-edge graph on 0–1, vertex 2 has no neighbour. -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_not_mem_single
    (x : Fin 3) (hx : s(2, x) ∈ ({s(0,1)} : Set (Sym2 (Fin 3)))) : False := by
  fin_cases x <;> simp_all

/-- The path 1–0–2 has no hop: both leaves would have to be sent to the middle vertex 0. -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_hop_free_path_a
    (h : Equiv.Perm (Fin 3)) :
    ¬ simple_graph_is_hop (SimpleGraph.fromEdgeSet ({s(0,1), s(0,2)} : Set (Sym2 (Fin 3)))) h := by
  intro hh
  have h1 := hh 1
  rw [SimpleGraph.fromEdgeSet_adj] at h1
  have h2 := hh 2
  rw [SimpleGraph.fromEdgeSet_adj] at h2
  exact absurd (h.injective ((simple_graph_completeGraph_three_leap_closed_not_intersection_closed_mem_path_a (h 1) h1.1).trans (simple_graph_completeGraph_three_leap_closed_not_intersection_closed_mem_path_b (h 2) h2.1).symm)) (by decide)

/-- The path 0–1–2 has no hop: both leaves would have to be sent to the middle vertex 1. -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_hop_free_path_b
    (h : Equiv.Perm (Fin 3)) :
    ¬ simple_graph_is_hop (SimpleGraph.fromEdgeSet ({s(0,1), s(1,2)} : Set (Sym2 (Fin 3)))) h := by
  intro hh
  have h1 := hh 0
  rw [SimpleGraph.fromEdgeSet_adj] at h1
  have h2 := hh 2
  rw [SimpleGraph.fromEdgeSet_adj] at h2
  exact absurd (h.injective ((simple_graph_completeGraph_three_leap_closed_not_intersection_closed_mem_path_c (h 0) h1.1).trans (simple_graph_completeGraph_three_leap_closed_not_intersection_closed_mem_path_d (h 2) h2.1).symm)) (by decide)

/-- The graph with the single edge 0–1 has no hop (vertex 2 is isolated). -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_hop_free_single
    (h : Equiv.Perm (Fin 3)) :
    ¬ simple_graph_is_hop (SimpleGraph.fromEdgeSet ({s(0,1)} : Set (Sym2 (Fin 3)))) h := by
  intro hh
  have h2 := hh 2
  rw [SimpleGraph.fromEdgeSet_adj] at h2
  exact simple_graph_completeGraph_three_leap_closed_not_intersection_closed_not_mem_single (h 2) h2.1

/-- A hop-free graph has trivial leap group. -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_leap_group_eq_bot
    (G : SimpleGraph (Fin 3)) (hG : ∀ h, ¬ simple_graph_is_hop G h) :
    simple_graph_leap_group G = ⊥ := by
  rw [simple_graph_leap_group, Subgroup.closure_eq_bot_iff]
  intro h hh
  exact absurd hh (hG h)

/-- The three edges of `K₃` on `Fin 3` are `{0,1}`, `{0,2}` and `{1,2}`. -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_edge_cases
    (e : Sym2 (Fin 3)) (he : e ∈ (⊤ : SimpleGraph (Fin 3)).edgeSet) :
    e = s(0,1) ∨ e = s(0,2) ∨ e = s(1,2) := by
  rw [SimpleGraph.edgeSet_top] at he
  induction e using Sym2.ind with
  | h a b =>
    simp only [Set.mem_compl_iff, Sym2.mem_diagSet, Sym2.mk_isDiag_iff] at he
    fin_cases a <;> fin_cases b <;> simp_all

/-- A pair of distinct vertices of `Fin 3` is one of the three edges of `K₃`. -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_mem_three_edges
    (v w : Fin 3) :
    s(v, w) ∈ ({s(0,1), s(0,2), s(1,2)} : Set (Sym2 (Fin 3))) ↔ v ≠ w := by
  fin_cases v <;> fin_cases w <;> simp_all

/-- Any edge set containing the three edges of `K₃` gives the complete graph. -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_fromEdgeSet_eq_top
    (S : Set (Sym2 (Fin 3)))
    (hS : ({s(0,1), s(0,2), s(1,2)} : Set (Sym2 (Fin 3))) ⊆ S) :
    SimpleGraph.fromEdgeSet S = ⊤ := by
  ext v w
  rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.top_adj]
  exact ⟨fun h => h.2, fun h => ⟨hS (by rw [simple_graph_completeGraph_three_leap_closed_not_intersection_closed_mem_three_edges]; exact h), h⟩⟩

/-- The leap group of `K₃` is nontrivial: the 3-cycle is a hop. -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_leap_group_top_ne_bot :
    simple_graph_leap_group (⊤ : SimpleGraph (Fin 3)) ≠ ⊥ := by
  intro hbot
  have hmem : finRotate 3 ∈ simple_graph_leap_group (⊤ : SimpleGraph (Fin 3)) :=
    simple_graph_is_hop_mem_leap_group _ _ (by
      intro v
      rw [SimpleGraph.top_adj]
      fin_cases v <;> decide)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact absurd hmem (by decide)

/-- The two spanning paths `{0,1},{0,2}` and `{0,1},{1,2}` meet in the single edge `{0,1}`. -/
private lemma simple_graph_completeGraph_three_leap_closed_not_intersection_closed_inter_eq :
    (({s(0,1), s(0,2)} : Set (Sym2 (Fin 3))) ∩ {s(0,1), s(1,2)}) = {s(0,1)} := by
  ext x
  induction x using Sym2.ind with
  | h a b => fin_cases a <;> fin_cases b <;> simp_all

/-- Leap-closed edge subsets of K₃ are not closed under intersection. -/
theorem simple_graph_completeGraph_three_leap_closed_not_intersection_closed :
    ∃ F₁ F₂ : Set (Sym2 (Fin 3)),
      simple_graph_is_leap_closed (⊤ : SimpleGraph (Fin 3)) F₁ ∧
      simple_graph_is_leap_closed (⊤ : SimpleGraph (Fin 3)) F₂ ∧
      ¬ simple_graph_is_leap_closed (⊤ : SimpleGraph (Fin 3)) (F₁ ∩ F₂) := by
  refine ⟨({s(0,1), s(0,2)} : Set (Sym2 (Fin 3))), ({s(0,1), s(1,2)} : Set (Sym2 (Fin 3))), ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] <;> decide
    · intro e he
      obtain ⟨heE, heF⟩ := he
      have he12 : e = s(1,2) := by
        rcases simple_graph_completeGraph_three_leap_closed_not_intersection_closed_edge_cases e heE with h | h | h
        · rw [h] at heF; simp at heF
        · rw [h] at heF; simp at heF
        · exact h
      rw [simple_graph_completeGraph_three_leap_closed_not_intersection_closed_leap_group_eq_bot _ simple_graph_completeGraph_three_leap_closed_not_intersection_closed_hop_free_path_a, he12, bot_lt_iff_ne_bot]
      have hg : SimpleGraph.fromEdgeSet (insert s(1,2) ({s(0,1), s(0,2)} : Set (Sym2 (Fin 3)))) = ⊤ :=
        simple_graph_completeGraph_three_leap_closed_not_intersection_closed_fromEdgeSet_eq_top _ (by intro x hx; simp at hx ⊢; tauto)
      rw [hg]
      exact simple_graph_completeGraph_three_leap_closed_not_intersection_closed_leap_group_top_ne_bot
  · refine ⟨?_, ?_⟩
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] <;> decide
    · intro e he
      obtain ⟨heE, heF⟩ := he
      have he02 : e = s(0,2) := by
        rcases simple_graph_completeGraph_three_leap_closed_not_intersection_closed_edge_cases e heE with h | h | h
        · rw [h] at heF; simp at heF
        · exact h
        · rw [h] at heF; simp at heF
      rw [simple_graph_completeGraph_three_leap_closed_not_intersection_closed_leap_group_eq_bot _ simple_graph_completeGraph_three_leap_closed_not_intersection_closed_hop_free_path_b, he02, bot_lt_iff_ne_bot]
      have hg : SimpleGraph.fromEdgeSet (insert s(0,2) ({s(0,1), s(1,2)} : Set (Sym2 (Fin 3)))) = ⊤ :=
        simple_graph_completeGraph_three_leap_closed_not_intersection_closed_fromEdgeSet_eq_top _ (by intro x hx; simp at hx ⊢; tauto)
      rw [hg]
      exact simple_graph_completeGraph_three_leap_closed_not_intersection_closed_leap_group_top_ne_bot
  · rw [simple_graph_completeGraph_three_leap_closed_not_intersection_closed_inter_eq]
    simp only [simple_graph_is_leap_closed]
    rintro ⟨-, hcond⟩
    have hmem : s(0,2) ∈ (⊤ : SimpleGraph (Fin 3)).edgeSet \ ({s(0,1)} : Set (Sym2 (Fin 3))) := by
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]; decide
      · simp
    have hlt := hcond s(0,2) hmem
    rw [simple_graph_completeGraph_three_leap_closed_not_intersection_closed_leap_group_eq_bot _ simple_graph_completeGraph_three_leap_closed_not_intersection_closed_hop_free_single] at hlt
    have hg : SimpleGraph.fromEdgeSet (insert s(0,2) ({s(0,1)} : Set (Sym2 (Fin 3))))
        = SimpleGraph.fromEdgeSet ({s(0,1), s(0,2)} : Set (Sym2 (Fin 3))) := by
      congr 1
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hg, simple_graph_completeGraph_three_leap_closed_not_intersection_closed_leap_group_eq_bot _ simple_graph_completeGraph_three_leap_closed_not_intersection_closed_hop_free_path_a] at hlt
    exact lt_irrefl ⊥ hlt
