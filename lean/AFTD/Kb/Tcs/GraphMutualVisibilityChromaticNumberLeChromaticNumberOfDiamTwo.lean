import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMutualVisibilityChromaticNumber
import AFTD.Kb.Tcs.GraphIsMutualVisibilityColorable
import AFTD.Kb.Tcs.GraphIsMutualVisibilitySet

/-!
# graph_mutual_visibility_chromatic_number_le_chromatic_number_of_diam_two

Topic: graphs   Node: 2692416456e9

Provenance: formalization of a published result. Source: arXiv:2610.39430, Proposition 1.2

For every finite simple graph G of diameter 2, the mutual-visibility chromatic number of G is at most the chromatic number of G.
-/

lemma graph_mutual_visibility_chromatic_number_le_chromatic_number_of_diam_two_is_mutual_visibility_set_of_indep
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hdiam : G.diam = 2)
    (S : Set V) (hS : ∀ u v, u ∈ S → v ∈ S → ¬ G.Adj u v) :
    graph_is_mutual_visibility_set G S := by
  have hne : G.diam ≠ 0 := by rw [hdiam]; decide
  have : Nontrivial V := G.nontrivial_of_diam_ne_zero hne
  have hconn : G.Connected := G.connected_iff_diam_ne_zero.mpr hne
  have hediam : G.ediam ≠ ⊤ := G.ediam_ne_top_of_diam_ne_zero hne
  intro u hu v hv
  by_cases huv : u = v
  · subst huv
    use SimpleGraph.Walk.nil
    refine ⟨by simp, ?_⟩
    intro x hx _
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    exact Or.inl hx
  · have hnotadj : ¬ G.Adj u v := hS u v hu hv
    have hdist_le : G.dist u v ≤ 2 := by
      have := G.dist_le_diam hediam (u := u) (v := v)
      rwa [hdiam] at this
    have hdist_gt : 1 < G.dist u v := hconn.one_lt_dist_of_ne_of_not_adj huv hnotadj
    have hdist_eq : G.dist u v = 2 := by omega
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
    have hp_len : p.length = 2 := hp.trans hdist_eq
    obtain ⟨w, h1, h2, hp_eq⟩ : ∃ (w : V) (h1 : G.Adj u w) (h2 : G.Adj w v),
      p = SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil) := by
      cases p with
      | nil => contradiction
      | cons h1 p1 =>
        cases p1 with
        | nil =>
          simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hp_len
          contradiction
        | cons h2 p2 =>
          cases p2 with
          | nil => exact ⟨_, h1, h2, rfl⟩
          | cons h3 p3 =>
            simp only [SimpleGraph.Walk.length_cons] at hp_len
            omega
    subst hp_eq
    refine ⟨_, hp, ?_⟩
    intro x hx hxS
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hxu | hxw | hxv
    · exact Or.inl hxu
    · have hx_adj : G.Adj u x := hxw ▸ h1
      have hnot : ¬ G.Adj u x := hS u x hu hxS
      exact (hnot hx_adj).elim
    · exact Or.inr hxv

lemma graph_mutual_visibility_chromatic_number_le_chromatic_number_of_diam_two_mv_colorable_of_colorable
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hdiam : G.diam = 2)
    {n : ℕ} (hc : G.Colorable n) :
    graph_is_mutual_visibility_colorable G n := by
  obtain ⟨c⟩ := hc
  refine ⟨c, fun i ↦ ?_⟩
  apply graph_mutual_visibility_chromatic_number_le_chromatic_number_of_diam_two_is_mutual_visibility_set_of_indep G hdiam
  intro u v hu hv hadj
  have hcu : c u = i := hu
  have hcv : c v = i := hv
  have hne : c u ≠ c v := c.valid hadj
  rw [hcu, hcv] at hne
  exact hne rfl

/-- In any finite diameter-2 graph, χ_μ(G) ≤ χ(G). -/
theorem graph_mutual_visibility_chromatic_number_le_chromatic_number_of_diam_two
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hdiam : G.diam = 2) :
    graph_mutual_visibility_chromatic_number G ≤ G.chromaticNumber := by
  change (⨅ n ∈ {n : ℕ | graph_is_mutual_visibility_colorable G n}, (n : ℕ∞)) ≤
    ⨅ n ∈ Set.ofPred G.Colorable, (n : ℕ∞)
  apply biInf_mono
  intro n hn
  exact graph_mutual_visibility_chromatic_number_le_chromatic_number_of_diam_two_mv_colorable_of_colorable G hdiam hn
