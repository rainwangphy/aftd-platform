import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStarLikeDeletionNumber
import AFTD.Kb.Tcs.SimpleGraphAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphIsStarLikeCompleteTwo
import AFTD.Kb.Tcs.SimpleGraphIsStarLike
import AFTD.Kb.Tcs.SimpleGraphDominatingSets

/-!
# dominating_average_star_like_vertex_stability_of_card_two

Topic: graphs   Node: be4bf680e91c

Provenance: original. Related work: arXiv:2208.10475v2: The average size of a dominating set in a graph

For every finite simple graph G on 2 vertices with no isolated vertex, the stability inequality 5 d_*(G) ≤ 51 (2·2/3 - avd(G)) holds.
-/

private lemma dominating_average_star_like_vertex_stability_of_card_two_univ_pair {V : Type*}
    [Fintype V] [DecidableEq V] (hV : Fintype.card V = 2)
    (a b : V) (hab : a ≠ b) : (Finset.univ : Finset V) = {a, b} := by
  have h2 : ({a, b} : Finset V).card = 2 := by simp [hab]
  exact (Finset.eq_univ_of_card _ (by rw [h2, hV])).symm

private lemma dominating_average_star_like_vertex_stability_of_card_two_complete {V : Type*}
    [Fintype V] [DecidableEq V] (hV : Fintype.card V = 2)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hiso : ∀ w, 0 < G.degree w) :
    ∀ x y : V, x ≠ y → G.Adj x y := by
  intro x y hxy
  obtain ⟨w, hw⟩ := (SimpleGraph.degree_pos_iff_exists_adj G x).mp (hiso x)
  have hwne : w ≠ x := (G.ne_of_adj hw).symm
  have hmem : w ∈ ({x, y} : Finset V) := by
    rw [← dominating_average_star_like_vertex_stability_of_card_two_univ_pair hV x y hxy]
    exact Finset.mem_univ w
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exact absurd h hwne
  · rw [h] at hw
    exact hw

private lemma dominating_average_star_like_vertex_stability_of_card_two_star {W : Type*}
    [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hcard : Fintype.card W = 2) (hcomp : ∀ a b, a ≠ b → H.Adj a b) :
    simple_graph_is_star_like H := by
  intro w
  left
  have hneigh : H.neighborFinset w = (Finset.univ : Finset W).erase w := by
    ext u
    rw [SimpleGraph.neighborFinset_eq_filter, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨(H.ne_of_adj h).symm, Finset.mem_univ u⟩
    · rintro ⟨hne, -⟩
      exact ⟨Finset.mem_univ u, hcomp w u (fun huw => hne huw.symm)⟩
  rw [SimpleGraph.degree, hneigh, Finset.card_erase_of_mem (Finset.mem_univ w),
    Finset.card_univ, hcard]

private lemma dominating_average_star_like_vertex_stability_of_card_two_del {V : Type*}
    [Fintype V] [DecidableEq V] (hV : Fintype.card V = 2)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hiso : ∀ w, 0 < G.degree w) :
    simple_graph_star_like_deletion_number G = 0 := by
  have hcomp := dominating_average_star_like_vertex_stability_of_card_two_complete hV G hiso
  rw [simple_graph_star_like_deletion_number, Nat.sInf_eq_zero]
  left
  refine ⟨∅, ?_, rfl⟩
  have hcardW : Fintype.card {v : V // v ∈ ((↑(∅ : Finset V)) : Set V)ᶜ} = 2 := by
    simpa using hV
  exact dominating_average_star_like_vertex_stability_of_card_two_star
    (H := SimpleGraph.induce ((↑(∅ : Finset V))ᶜ) G) hcardW
    (fun a b hab => hcomp a.val b.val (fun h => hab (Subtype.ext h)))

private lemma dominating_average_star_like_vertex_stability_of_card_two_sum_univ {V : Type*}
    [Fintype V] [DecidableEq V] (hV : Fintype.card V = 2) :
    (∑ S ∈ (Finset.univ : Finset (Finset V)), (S.card : ℚ)) = 4 := by
  have h2 : ((∑ S ∈ (Finset.univ : Finset (Finset V)), S.card : ℕ) : ℚ) = 4 := by
    have h := Finset.sum_powerset_apply_card (fun n : ℕ => n) (x := (Finset.univ : Finset V))
    rw [← Finset.powerset_univ (α := V), h]
    simp only [Finset.card_univ, hV]
    decide
  simpa using h2

private lemma dominating_average_star_like_vertex_stability_of_card_two_dom_iff {V : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcomp : ∀ x y : V, x ≠ y → G.Adj x y) (S : Finset V) :
    S ∈ simple_graph_dominating_sets G ↔ S.Nonempty := by
  constructor
  · rintro h
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    have key : (∅ : Finset V) ∈ simple_graph_dominating_sets G := h0 ▸ h
    simp only [simple_graph_dominating_sets, Finset.mem_filter, Finset.mem_univ,
      true_and] at key
    have := key (Classical.arbitrary V)
    simp at this
  · intro h
    simp only [simple_graph_dominating_sets, Finset.mem_filter, Finset.mem_univ, true_and]
    intro w
    obtain ⟨u, hu⟩ := h
    by_cases hw : w ∈ S
    · exact Or.inl hw
    · exact Or.inr ⟨u, hu, hcomp u w (fun huw => hw (huw ▸ hu))⟩

private lemma dominating_average_star_like_vertex_stability_of_card_two_avd {V : Type*}
    [Fintype V] [DecidableEq V] (hV : Fintype.card V = 2)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hiso : ∀ w, 0 < G.degree w) :
    simple_graph_avg_dominating_order G = 4 / 3 := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by rw [hV]; norm_num)
  haveI := hne
  have hcomp := dominating_average_star_like_vertex_stability_of_card_two_complete hV G hiso
  have hdom : simple_graph_dominating_sets G = (Finset.univ : Finset (Finset V)).erase ∅ := by
    ext S
    rw [dominating_average_star_like_vertex_stability_of_card_two_dom_iff G hcomp S,
      Finset.mem_erase, Finset.nonempty_iff_ne_empty]
    simp
  have hsum : (∑ S ∈ simple_graph_dominating_sets G, (S.card : ℚ)) = 4 := by
    rw [hdom, Finset.sum_erase (s := (Finset.univ : Finset (Finset V)))
      (f := fun S => (S.card : ℚ)) (a := (∅ : Finset V)) (by simp)]
    exact dominating_average_star_like_vertex_stability_of_card_two_sum_univ hV
  have hcard : (simple_graph_dominating_sets G).card = 3 := by
    rw [hdom, Finset.card_erase_of_mem (Finset.mem_univ (∅ : Finset V)), Finset.card_univ,
      Fintype.card_finset, hV]
    norm_num
  rw [simple_graph_avg_dominating_order, hsum, hcard]
  norm_num

/-- The stability inequality holds at order n = 2. -/
theorem dominating_average_star_like_vertex_stability_of_card_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 2)
    (hiso : ∀ w, 0 < G.degree w) :
    5 * (simple_graph_star_like_deletion_number G : ℚ) ≤
      51 * (2 * (Fintype.card V : ℚ) / 3 - simple_graph_avg_dominating_order G) := by
  rw [dominating_average_star_like_vertex_stability_of_card_two_del hcard G hiso,
    dominating_average_star_like_vertex_stability_of_card_two_avd hcard G hiso, hcard]
  norm_num
