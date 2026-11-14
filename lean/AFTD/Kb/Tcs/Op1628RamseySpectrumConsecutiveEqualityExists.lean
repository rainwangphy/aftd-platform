import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyNumber
import AFTD.Kb.Tcs.SupportGraph
import AFTD.Kb.Tcs.SetColoringRamseyProperty

/-!
# op_1628_ramsey_spectrum_consecutive_equality_exists

Topic: combinatorics   Node: 63546c794103

Provenance: formalization of a published result. Source: arXiv:2611.15376 Question 7.1

There exists a type V with a Fintype instance, a simple graph G on V such that G is connected and has at least two edges, and natural numbers r, s, t with 1 ≤ t, t < s, and s ≤ r such that set_coloring_ramsey_number G r s t = set_coloring_ramsey_number G r s (t + 1).
-/

open scoped Classical in
lemma op_1628_ramsey_spectrum_consecutive_equality_exists_support_graph_eq_top {N r : ℕ}
    (ϕ : (⊤ : SimpleGraph (Fin N)).edgeSet → Finset (Fin r))
    (T : Finset (Fin r)) (h : ∀ e, T ⊆ ϕ e) :
    support_graph ϕ T = (⊤ : SimpleGraph (Fin N)) := by
  have hset : {e : Sym2 (Fin N) | ∃ hh : e ∈ (⊤ : SimpleGraph (Fin N)).edgeSet, T ⊆ ϕ ⟨e, hh⟩}
      = (⊤ : SimpleGraph (Fin N)).edgeSet := by
    ext e
    constructor
    · rintro ⟨hh, -⟩; exact hh
    · intro he; exact ⟨he, h ⟨e, he⟩⟩
  unfold support_graph
  rw [hset, SimpleGraph.fromEdgeSet_edgeSet]

open scoped Classical in
lemma op_1628_ramsey_spectrum_consecutive_equality_exists_prop_one_iff {N : ℕ} (G : SimpleGraph (Fin 3)) :
    set_coloring_ramsey_property G 2 2 1 N ↔ SimpleGraph.IsContained G (⊤ : SimpleGraph (Fin N)) := by
  constructor
  · intro h
    have hϕ : ∀ e : (⊤ : SimpleGraph (Fin N)).edgeSet, ((fun _ => (Finset.univ : Finset (Fin 2))) e).card = 2 := by
      intro e; simp
    obtain ⟨T, hTcard, hTcont⟩ := h (fun _ => Finset.univ) hϕ
    have htop : support_graph (fun _ => (Finset.univ : Finset (Fin 2))) T = (⊤ : SimpleGraph (Fin N)) := by
      apply op_1628_ramsey_spectrum_consecutive_equality_exists_support_graph_eq_top; intro e; simp
    rwa [htop] at hTcont
  · intro h ϕ hϕ
    refine ⟨{0}, ?_, ?_⟩
    · simp
    · have htop : support_graph ϕ {0} = (⊤ : SimpleGraph (Fin N)) := by
        apply op_1628_ramsey_spectrum_consecutive_equality_exists_support_graph_eq_top
        intro e
        have hc : ϕ e = Finset.univ := Finset.eq_univ_of_card _ (by simpa using hϕ e)
        rw [hc]; exact Finset.subset_univ _
      rw [htop]; exact h

open scoped Classical in
lemma op_1628_ramsey_spectrum_consecutive_equality_exists_prop_two_iff {N : ℕ} (G : SimpleGraph (Fin 3)) :
    set_coloring_ramsey_property G 2 2 2 N ↔ SimpleGraph.IsContained G (⊤ : SimpleGraph (Fin N)) := by
  constructor
  · intro h
    have hϕ : ∀ e : (⊤ : SimpleGraph (Fin N)).edgeSet, ((fun _ => (Finset.univ : Finset (Fin 2))) e).card = 2 := by
      intro e; simp
    obtain ⟨T, hTcard, hTcont⟩ := h (fun _ => Finset.univ) hϕ
    have htop : support_graph (fun _ => (Finset.univ : Finset (Fin 2))) T = (⊤ : SimpleGraph (Fin N)) := by
      apply op_1628_ramsey_spectrum_consecutive_equality_exists_support_graph_eq_top; intro e; simp
    rwa [htop] at hTcont
  · intro h ϕ hϕ
    refine ⟨Finset.univ, ?_, ?_⟩
    · simp
    · have htop : support_graph ϕ (Finset.univ : Finset (Fin 2)) = (⊤ : SimpleGraph (Fin N)) := by
        apply op_1628_ramsey_spectrum_consecutive_equality_exists_support_graph_eq_top
        intro e
        have hc : ϕ e = Finset.univ := Finset.eq_univ_of_card _ (by simpa using hϕ e)
        rw [hc]
      rw [htop]; exact h

open scoped Classical in
lemma op_1628_ramsey_spectrum_consecutive_equality_exists_two_le_pathGraph_edgeFinset
    (i : Fintype ↑(SimpleGraph.pathGraph 3).edgeSet) :
    2 ≤ (@SimpleGraph.edgeFinset (Fin 3) (SimpleGraph.pathGraph 3) i).card := by
  have h01 : (s(0, 1) : Sym2 (Fin 3)) ∈ (SimpleGraph.pathGraph 3).edgeSet := by
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.pathGraph_adj]
    left; norm_num
  have h12 : (s(1, 2) : Sym2 (Fin 3)) ∈ (SimpleGraph.pathGraph 3).edgeSet := by
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.pathGraph_adj]
    left; norm_num
  have hne : (s(0, 1) : Sym2 (Fin 3)) ≠ s(1, 2) := by
    intro h
    have hm : (0 : Fin 3) ∈ (s(1, 2) : Sym2 (Fin 3)) := by
      rw [← h]; rw [Sym2.mem_iff]; left; rfl
    rw [Sym2.mem_iff] at hm
    rcases hm with h0 | h0
    · exact absurd h0 (by decide)
    · exact absurd h0 (by decide)
  have hsub : ({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) ⊆
      @SimpleGraph.edgeFinset (Fin 3) (SimpleGraph.pathGraph 3) i := by
    intro e he
    rw [@SimpleGraph.mem_edgeFinset (Fin 3) (SimpleGraph.pathGraph 3) e i]
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact h01
    · exact h12
  have hcard : ({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))).card = 2 := Finset.card_pair hne
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  exact hle

open scoped Classical in
/-- Existence of a connected graph with at least two edges and palette parameters yielding equality in consecutive terms of the Ramsey intersection spectrum. -/
theorem op_1628_ramsey_spectrum_consecutive_equality_exists :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.Connected ∧ 2 ≤ G.edgeFinset.card ∧
      ∃ (r s t : ℕ), 1 ≤ t ∧ t < s ∧ s ≤ r ∧
        set_coloring_ramsey_number G r s t = set_coloring_ramsey_number G r s (t + 1) := by
  refine ⟨Fin 3, inferInstance, SimpleGraph.pathGraph 3, ?_, ?_, 2, 2, 1, ?_, ?_, ?_, ?_⟩
  · have := SimpleGraph.pathGraph_connected 2
    simpa using this
  · exact op_1628_ramsey_spectrum_consecutive_equality_exists_two_le_pathGraph_edgeFinset _
  · norm_num
  · norm_num
  · norm_num
  · show sInf {N : ℕ | set_coloring_ramsey_property (SimpleGraph.pathGraph 3) 2 2 1 N}
       = sInf {N : ℕ | set_coloring_ramsey_property (SimpleGraph.pathGraph 3) 2 2 2 N}
    have hset : {N : ℕ | set_coloring_ramsey_property (SimpleGraph.pathGraph 3) 2 2 1 N}
        = {N : ℕ | set_coloring_ramsey_property (SimpleGraph.pathGraph 3) 2 2 2 N} := by
      ext N
      exact (op_1628_ramsey_spectrum_consecutive_equality_exists_prop_one_iff (N := N) _).trans
        (op_1628_ramsey_spectrum_consecutive_equality_exists_prop_two_iff (N := N) _).symm
    rw [hset]
