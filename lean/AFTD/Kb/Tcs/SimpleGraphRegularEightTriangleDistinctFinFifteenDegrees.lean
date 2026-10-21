import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleDegreeLeChoose
import AFTD.Kb.Tcs.SimpleGraphComplRegularTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphTriangleDegreeCompl

/-!
# simple_graph_regular_eight_triangle_distinct_fin_fifteen_degrees

Topic: graphs   Node: e515360351f7

Provenance: helper lemma. step towards exists_nonempty_regular_eight_triangle_distinct

If G is an 8-regular triangle-distinct graph on the 15 vertices {0,…,14}, then the set of its vertex triangle-degrees is exactly {5,6,…,19}: the triangle-degrees are 15 distinct integers, each between 4 and 19, and the value 4 is impossible.
-/

lemma simple_graph_regular_eight_triangle_distinct_fin_fifteen_degrees_no_fifteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : H.IsRegularOfDegree 6) (htd : simple_graph_is_triangle_distinct H) (v : V) :
    simple_graph_triangle_degree H v ≠ 15 := by
  intro htd_v
  have hdeg_v : H.degree v = 6 := hreg v
  have hclique : ∀ x ∈ H.neighborFinset v, ∀ y ∈ H.neighborFinset v, x ≠ y → H.Adj x y := by
    have hcard : ((H.neighborFinset v).powersetCard 2).card = 15 := by
      rw [Finset.card_powersetCard, SimpleGraph.card_neighborFinset_eq_degree, hdeg_v]
      rfl
    have hsub : ((H.neighborFinset v).powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → H.Adj x y) ⊆
        (H.neighborFinset v).powersetCard 2 := Finset.filter_subset _ _
    have heq : ((H.neighborFinset v).powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → H.Adj x y) =
        (H.neighborFinset v).powersetCard 2 := by
      apply Finset.eq_of_subset_of_card_le hsub
      unfold simple_graph_triangle_degree at htd_v
      rw [htd_v, hcard]
    intro x hx y hy hxy
    have hs : {x, y} ∈ (H.neighborFinset v).powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      · rw [Finset.card_pair hxy]
    have hs_in : {x, y} ∈ ((H.neighborFinset v).powersetCard 2).filter (fun s => ∀ a ∈ s, ∀ b ∈ s, a ≠ b → H.Adj a b) := by
      rw [heq]
      exact hs
    rw [Finset.mem_filter] at hs_in
    apply hs_in.2 x (by simp) y (by simp) hxy

  have hcard_v : (H.neighborFinset v).card = 6 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg_v]
  have hnonempty : (H.neighborFinset v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty
    rw [h_empty] at hcard_v
    contradiction
  obtain ⟨u, hu⟩ := hnonempty
  have hvu : H.Adj v u := (H.mem_neighborFinset v u).mp hu
  have huv : H.Adj u v := hvu.symm
  have hne_uv : u ≠ v := huv.ne
  have hdeg_u : H.degree u = 6 := hreg u

  have hsub_u : insert v (H.neighborFinset v \ {u}) ⊆ H.neighborFinset u := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hw
    rcases hw with rfl | ⟨hw_v, hw_ne_u⟩
    · rw [SimpleGraph.mem_neighborFinset]
      exact huv
    · rw [SimpleGraph.mem_neighborFinset]
      apply hclique u hu w hw_v (Ne.symm hw_ne_u)

  have hcard_sub : (insert v (H.neighborFinset v \ {u})).card = 6 := by
    have hv_not_in : v ∉ H.neighborFinset v \ {u} := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton, not_and]
      intro hv_in
      have : H.Adj v v := (H.mem_neighborFinset v v).mp hv_in
      exact (H.irrefl this).elim
    rw [Finset.card_insert_of_notMem hv_not_in]
    have hu_in : {u} ⊆ H.neighborFinset v := by
      rw [Finset.singleton_subset_iff]
      exact hu
    rw [Finset.card_sdiff_of_subset hu_in, Finset.card_singleton, hcard_v]

  have heq_u : insert v (H.neighborFinset v \ {u}) = H.neighborFinset u := by
    apply Finset.eq_of_subset_of_card_le hsub_u
    rw [hcard_sub, SimpleGraph.card_neighborFinset_eq_degree, hdeg_u]

  have hclique_u : ∀ x ∈ H.neighborFinset u, ∀ y ∈ H.neighborFinset u, x ≠ y → H.Adj x y := by
    intro x hx y hy hxy
    rw [← heq_u] at hx hy
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hx hy
    rcases hx with rfl | ⟨hx_v, -⟩
    · rcases hy with rfl | ⟨hy_v, -⟩
      · contradiction
      · rw [SimpleGraph.mem_neighborFinset] at hy_v
        exact hy_v
    · rcases hy with rfl | ⟨hy_v, -⟩
      · rw [SimpleGraph.mem_neighborFinset] at hx_v
        exact hx_v.symm
      · exact hclique x hx_v y hy_v hxy

  have htd_u : simple_graph_triangle_degree H u = 15 := by
    unfold simple_graph_triangle_degree
    have heq_filter : ((H.neighborFinset u).powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → H.Adj x y) =
        (H.neighborFinset u).powersetCard 2 := by
      ext s
      simp only [Finset.mem_filter]
      refine ⟨fun h => h.1, fun hs => ⟨hs, ?_⟩⟩
      intro a ha b hb hab
      rw [Finset.mem_powersetCard] at hs
      exact hclique_u a (hs.1 ha) b (hs.1 hb) hab
    rw [heq_filter, Finset.card_powersetCard, SimpleGraph.card_neighborFinset_eq_degree, hdeg_u]
    rfl

  have heq_td : simple_graph_triangle_degree H u = simple_graph_triangle_degree H v := by
    rw [htd_u, htd_v]
  have hu_eq_v := htd heq_td
  exact hne_uv hu_eq_v

/-- An 8-regular triangle-distinct graph on 15 vertices has triangle-degree set exactly {5,…,19}. -/
theorem simple_graph_regular_eight_triangle_distinct_fin_fifteen_degrees
    (G : SimpleGraph (Fin 15)) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 8) (htd : simple_graph_is_triangle_distinct G) :
    Finset.image (simple_graph_triangle_degree G) Finset.univ = Finset.Icc 5 19 := by
  have hN : Fintype.card (Fin 15) = 15 := Fintype.card_fin 15
  have hcompl := simple_graph_compl_regular_triangle_distinct G 8 15 hN hreg htd
  have hreg_c : Gᶜ.IsRegularOfDegree 6 := hcompl.1
  have htd_c : simple_graph_is_triangle_distinct Gᶜ := hcompl.2

  have hsum : ∀ v : Fin 15, simple_graph_triangle_degree G v + simple_graph_triangle_degree Gᶜ v = 19 := by
    intro v
    have h := simple_graph_triangle_degree_compl G 8 15 hN hreg v
    have hc : (15 - 8 - 1).choose 2 = 15 := rfl
    have h2 : ((15 - 8 - 1).choose 2 : ℚ) - (15 * 8 : ℚ) / 2 + (8 : ℚ) ^ 2 = 19 := by
      rw [hc]; norm_num
    have h3 : (simple_graph_triangle_degree Gᶜ v : ℚ) = 19 - simple_graph_triangle_degree G v := by
      calc (simple_graph_triangle_degree Gᶜ v : ℚ)
        _ = ((15 - 8 - 1).choose 2 : ℚ) - (15 * 8 : ℚ) / 2 + (8 : ℚ) ^ 2 -
            simple_graph_triangle_degree G v := h
        _ = 19 - simple_graph_triangle_degree G v := by rw [h2]
    exact_mod_cast (by linarith : (simple_graph_triangle_degree G v : ℚ) + simple_graph_triangle_degree Gᶜ v = 19)

  have hsubset : Finset.image (simple_graph_triangle_degree G) Finset.univ ⊆ Finset.Icc 5 19 := by
    intro k hk
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hk
    obtain ⟨v, rfl⟩ := hk
    rw [Finset.mem_Icc]
    have hdeg_c_v : Gᶜ.degree v = 6 := hreg_c v
    have htd_c_le : simple_graph_triangle_degree Gᶜ v ≤ 15 := by
      have := simple_graph_triangle_degree_le_choose Gᶜ v
      rw [hdeg_c_v] at this
      exact this
    have htd_c_ne : simple_graph_triangle_degree Gᶜ v ≠ 15 :=
      simple_graph_regular_eight_triangle_distinct_fin_fifteen_degrees_no_fifteen Gᶜ hreg_c htd_c v
    have htd_c_le_14 : simple_graph_triangle_degree Gᶜ v ≤ 14 := by
      omega
    have hsv := hsum v
    constructor
    · omega
    · omega

  apply Finset.eq_of_subset_of_card_le hsubset
  have hcard_univ : (Finset.univ : Finset (Fin 15)).card = 15 := Fintype.card_fin 15
  have hinj : Function.Injective (simple_graph_triangle_degree G) := htd
  rw [Finset.card_image_of_injective Finset.univ hinj, hcard_univ, Nat.card_Icc]
