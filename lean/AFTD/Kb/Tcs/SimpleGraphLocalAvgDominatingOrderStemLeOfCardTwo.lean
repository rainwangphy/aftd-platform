import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphLeafNeighborCount
import AFTD.Kb.Tcs.SimpleGraphIsStarLike
import AFTD.Kb.Tcs.SimpleGraphDominatingSetsContaining

/-!
# simple_graph_local_avg_dominating_order_stem_le_of_card_two

Topic: graphs   Node: 5cafa7a6979a

Provenance: helper lemma. step towards simple_graph_local_avg_dominating_order_stem_le

The target statement at order n = 2: if |V| = 2 and G has no isolated vertices, then for every vertex v, avd_v(G) = (4·2+1)/6, v has exactly one leaf neighbour, and G is star-like (G is K2). This is the base case of the target, where the equality case of Conjecture 6.1 is attained.
-/

/-- On two vertices a graph without isolated vertices is K2, where v is a 1-stem in a star-like graph and avd_v = 3/2 = (4·2+1)/6: the target's equality case at the smallest order. -/
theorem simple_graph_local_avg_dominating_order_stem_le_of_card_two
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 2) (hiso : ∀ w, 0 < G.degree w) (v : V) :
    simple_graph_local_avg_dominating_order G v = (4 * (Fintype.card V : ℚ) + 1) / 6 ∧
      simple_graph_leaf_neighbor_count G v = 1 ∧ simple_graph_is_star_like G := by
  classical
  have hdeg : ∀ x : V, G.degree x = 1 := by
    intro x
    have hpos := hiso x
    have hlt := G.degree_lt_card_verts x
    omega
  obtain ⟨w, hvw, _⟩ := (G.degree_eq_one_iff_existsUnique_adj (v := v)).mp (hdeg v)
  have hvw_ne : v ≠ w := hvw.ne
  have hcover : ∀ x : V, x = v ∨ x = w := by
    intro x
    have hcardpair : ({v, w} : Finset V).card = 2 := Finset.card_pair hvw_ne
    have huniv : ({v, w} : Finset V) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcardpair, hcard]
    have hx : x ∈ ({v, w} : Finset V) := by
      rw [huniv]
      simp
    simpa using hx
  have hset : simple_graph_dominating_sets_containing G v = {({v} : Finset V), {v, w}} := by
    ext S
    simp only [simple_graph_dominating_sets_containing, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hS
      obtain ⟨hvS, hdom⟩ := hS
      by_cases hwS : w ∈ S
      · right
        apply Finset.Subset.antisymm
        · intro x hx
          rcases hcover x with rfl | rfl
          · simp
          · simp
        · intro x hx
          rcases (by simpa using hx : x = v ∨ x = w) with rfl | rfl
          · exact hvS
          · exact hwS
      · left
        apply Finset.Subset.antisymm
        · intro x hx
          rcases hcover x with rfl | rfl
          · simp
          · exact absurd hx hwS
        · intro x hx
          rcases (by simpa using hx : x = v) with rfl
          exact hvS
    · intro hS
      constructor
      · rcases hS with rfl | rfl <;> simp
      · intro x
        rcases hcover x with rfl | rfl
        · rcases hS with rfl | rfl <;> simp
        · rcases hS with rfl | rfl <;> simp [hvw]
  constructor
  · rw [simple_graph_local_avg_dominating_order, hset]
    have hsum :
        (∑ S ∈ ({({v} : Finset V), {v, w}} : Finset (Finset V)), (S.card : ℚ)) = 3 := by
      rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        simp [Finset.card_pair hvw_ne]
        norm_num
      · intro h
        simp only [Finset.mem_singleton] at h
        have hw : w ∈ ({v} : Finset V) := by
          rw [h]
          simp
        simp only [Finset.mem_singleton] at hw
        exact hvw_ne hw.symm
    have hcardfam : ({({v} : Finset V), {v, w}} : Finset (Finset V)).card = 2 := by
      rw [Finset.card_pair]
      intro h
      have hw : w ∈ ({v} : Finset V) := by
        rw [h]
        simp
      simp only [Finset.mem_singleton] at hw
      exact hvw_ne hw.symm
    rw [hsum, hcardfam]
    norm_num [hcard]
  constructor
  · simp [simple_graph_leaf_neighbor_count, hdeg]
  · intro x
    exact Or.inl (hdeg x)
