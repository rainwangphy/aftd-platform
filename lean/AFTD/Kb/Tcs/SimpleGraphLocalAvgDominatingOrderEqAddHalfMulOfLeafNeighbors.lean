import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrderEqHalfAddOfLeafNeighbor
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphDominatingSetsContaining

/-!
# simple_graph_local_avg_dominating_order_eq_add_half_mul_of_leaf_neighbors

Topic: graphs   Node: 603f52756817

Provenance: helper lemma. step towards simple_graph_local_avg_dominating_order_stem_le

If every member of a finite set L of vertices is a leaf neighbour of v (G.Adj v ℓ and deg ℓ = 1 for ℓ ∈ L), then avd_v(G) = |L|/2 + avd_v(G - L), where G - L is the subgraph induced on V \ L (which still contains v). This is the paper's identity D_v(G,x) = (1+x)^{|L|} D_v(G-L,x) differentiated at 1; it generalises the banked one-leaf recursion `simple_graph_local_avg_dominating_order_eq_half_add_of_leaf_neighbor` and is the step that reduces the l-stem case for l ≥ 2 to l = 2.
-/

lemma simple_graph_local_avg_dominating_order_eq_add_half_mul_of_leaf_neighbors_sum_powerset_card_rat
    {α : Type*} [DecidableEq α] (s : Finset α) :
    ∑ t ∈ s.powerset, (t.card : ℚ) = (s.card : ℚ) * (2 ^ s.card : ℚ) / 2 := by
  have h_inv : ∀ t ∈ s.powerset, s \ t ∈ s.powerset := by
    intro t ht
    rw [Finset.mem_powerset] at ht ⊢
    exact Finset.sdiff_subset
  have h_left : ∀ t ∈ s.powerset, s \ (s \ t) = t := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    exact Finset.sdiff_sdiff_eq_self ht
  have h_symm : (∑ t ∈ s.powerset, (t.card : ℚ)) = (∑ t ∈ s.powerset, ((s \ t).card : ℚ)) := by
    refine Finset.sum_nbij' (fun t => s \ t) (fun t => s \ t) h_inv h_inv h_left h_left ?_
    intro t ht
    rw [h_left t ht]
  have h_add : 2 * (∑ t ∈ s.powerset, (t.card : ℚ)) =
      ∑ t ∈ s.powerset, ((t.card : ℚ) + ((s \ t).card : ℚ)) := by
    calc 2 * (∑ t ∈ s.powerset, (t.card : ℚ))
      _ = (∑ t ∈ s.powerset, (t.card : ℚ)) + (∑ t ∈ s.powerset, (t.card : ℚ)) := by ring
      _ = (∑ t ∈ s.powerset, (t.card : ℚ)) + (∑ t ∈ s.powerset, ((s \ t).card : ℚ)) := by rw [h_symm]
      _ = ∑ t ∈ s.powerset, ((t.card : ℚ) + ((s \ t).card : ℚ)) := by rw [Finset.sum_add_distrib]
  have h_card : ∀ t ∈ s.powerset, (t.card : ℚ) + ((s \ t).card : ℚ) = (s.card : ℚ) := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    rw [add_comm, ← Nat.cast_add, Finset.card_sdiff_add_card_eq_card ht]
  have h_sum : (∑ t ∈ s.powerset, ((t.card : ℚ) + ((s \ t).card : ℚ))) =
      (2 ^ s.card : ℚ) * (s.card : ℚ) := by
    rw [Finset.sum_congr rfl h_card, Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
    push_cast; ring
  linarith

/-- Peeling several leaf neighbours at once: if L is a set of leaf neighbours of v then avd_v(G) = |L|/2 + avd of v in the subgraph induced on V \ L. With L a singleton this is the banked single-leaf recursion. -/
theorem simple_graph_local_avg_dominating_order_eq_add_half_mul_of_leaf_neighbors {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (L : Finset V) (hL : ∀ ℓ ∈ L, G.Adj v ℓ ∧ G.degree ℓ = 1) :
    simple_graph_local_avg_dominating_order G v = (L.card : ℚ) / 2 +
      simple_graph_local_avg_dominating_order (G.induce ((Finset.univ \ L : Finset V) : Set V))
        ⟨v, by
          simp only [Finset.coe_sdiff, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ, true_and]
          intro hmem
          exact (G.ne_of_adj (hL v hmem).1) rfl⟩ := by
  have hv : v ∈ (((Finset.univ \ L : Finset V) : Set V)) := by
    simp only [Finset.coe_sdiff, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ, true_and]
    intro hmem
    exact (G.ne_of_adj (hL v hmem).1) rfl
  set p : V → Prop := fun x => x ∈ (((Finset.univ \ L : Finset V) : Set V))
  set A : Set V := ((Finset.univ \ L : Finset V) : Set V)
  set H : SimpleGraph ↥A := G.induce A
  set D : Finset (Finset V) := simple_graph_dominating_sets_containing G v with hD
  set D' : Finset (Finset ↥A) := simple_graph_dominating_sets_containing H ⟨v, hv⟩ with hD'
  set toProd : Finset V → Finset ↥A × Finset V := fun S => (Finset.subtype p S, S ∩ L)
  set fromProd : Finset ↥A × Finset V → Finset V :=
    fun TX => Finset.map (Function.Embedding.subtype p) TX.1 ∪ TX.2

  have memD : ∀ S, S ∈ D ↔ v ∈ S ∧ ∀ w, w ∈ S ∨ ∃ u ∈ S, G.Adj u w := by
    intro S; rw [hD]; simp [simple_graph_dominating_sets_containing]
  have memD' : ∀ T, T ∈ D' ↔ ⟨v, hv⟩ ∈ T ∧ ∀ w : ↥A, w ∈ T ∨ ∃ u ∈ T, H.Adj u w := by
    intro T; rw [hD']; simp [simple_graph_dominating_sets_containing]

  have huniq : ∀ ℓ ∈ L, ∀ w : V, G.Adj ℓ w → w = v := by
    intro ℓ hℓ w hw
    obtain ⟨x, hx, hxu⟩ := (SimpleGraph.degree_eq_one_iff_existsUnique_adj (G := G) (v := ℓ)).mp (hL ℓ hℓ).2
    have hvx : v = x := hxu v (hL ℓ hℓ).1.symm
    have hwx : w = x := hxu w hw
    rw [hwx, ← hvx]

  have h_maps_to : ∀ S ∈ D, toProd S ∈ D' ×ˢ L.powerset := by
    intro S hS
    rw [Finset.mem_product, Finset.mem_powerset]
    refine ⟨?_, Finset.inter_subset_right⟩
    obtain ⟨hvS, hdom⟩ := (memD S).mp hS
    rw [memD']
    refine ⟨by rw [Finset.mem_subtype]; exact hvS, ?_⟩
    intro w
    rcases hdom w.1 with hwS | ⟨u, huS, huadj⟩
    · left; rw [Finset.mem_subtype]; exact hwS
    · by_cases huL : u ∈ L
      · have hwv : w.1 = v := huniq u huL w.1 huadj
        left; rw [Finset.mem_subtype]; rw [hwv]; exact hvS
      · right
        have hup : p u := by
          simp only [p, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact huL
        refine ⟨⟨u, hup⟩, by rw [Finset.mem_subtype]; exact huS, ?_⟩
        rw [SimpleGraph.induce_adj]
        exact huadj

  have h_maps_back : ∀ TX ∈ D' ×ˢ L.powerset, fromProd TX ∈ D := by
    rintro ⟨T, X⟩ hTX
    rw [Finset.mem_product, Finset.mem_powerset] at hTX
    obtain ⟨hT, -⟩ := hTX
    obtain ⟨hvT, hdom⟩ := (memD' T).mp hT
    rw [memD]
    have hvS : v ∈ fromProd (T, X) := by
      apply Finset.mem_union_left
      rw [Finset.mem_map]
      exact ⟨⟨v, hv⟩, hvT, rfl⟩
    refine ⟨hvS, ?_⟩
    intro w
    by_cases hwL : w ∈ L
    · right
      refine ⟨v, hvS, (hL w hwL).1⟩
    · have hwp : p w := by
        simp only [p, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact hwL
      rcases hdom ⟨w, hwp⟩ with hwT | ⟨u, huT, huadj⟩
      · left
        apply Finset.mem_union_left
        rw [Finset.mem_map]
        exact ⟨⟨w, hwp⟩, hwT, rfl⟩
      · right
        refine ⟨u.1, ?_, ?_⟩
        · apply Finset.mem_union_left
          rw [Finset.mem_map]
          exact ⟨u, huT, rfl⟩
        · exact huadj

  have h_left_inv : ∀ S ∈ D, fromProd (toProd S) = S := by
    intro S _
    dsimp [fromProd, toProd]
    rw [Finset.subtype_map]
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_inter, p, Finset.mem_coe,
      Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto

  have h_right_inv : ∀ TX ∈ D' ×ˢ L.powerset, toProd (fromProd TX) = TX := by
    rintro ⟨T, X⟩ hTX
    rw [Finset.mem_product, Finset.mem_powerset] at hTX
    obtain ⟨-, hX⟩ := hTX
    dsimp [fromProd, toProd]
    apply Prod.ext
    · ext ⟨a, ha⟩
      have ha_not : a ∉ L := by simpa [A] using ha
      simp only [Finset.mem_subtype, Finset.mem_union]
      constructor
      · rintro (hT | hX')
        · rw [Finset.mem_map] at hT
          obtain ⟨⟨b, hb⟩, hbT, rfl⟩ := hT
          exact hbT
        · exact False.elim (ha_not (hX hX'))
      · intro hT
        left
        rw [Finset.mem_map]
        exact ⟨⟨a, ha⟩, hT, rfl⟩
    · ext a
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hT | hX', haL⟩
        · rw [Finset.mem_map] at hT
          obtain ⟨⟨b, hb⟩, hbT, rfl⟩ := hT
          have hb_not : b ∉ L := by simpa [p] using hb
          exact False.elim (hb_not haL)
        · exact hX'
      · intro ha
        refine ⟨Or.inr ha, hX ha⟩

  have h_card_eq : D.card = D'.card * 2 ^ L.card := by
    have h := Finset.card_nbij' toProd fromProd h_maps_to h_maps_back h_left_inv h_right_inv
    rw [h, Finset.card_product, Finset.card_powerset]

  have h_sum_term : ∀ S ∈ D, (S.card : ℚ) = ((toProd S).1.card : ℚ) + ((toProd S).2.card : ℚ) := by
    intro S _
    dsimp [toProd]
    have h1 : (Finset.subtype p S).card = (S \ L).card := by
      rw [Finset.card_subtype]
      congr 1
      ext x
      simp [p]
    rw [h1, ← Nat.cast_add, add_comm]
    congr 1
    exact (Finset.card_inter_add_card_sdiff S L).symm

  have h_sum_nbij := Finset.sum_nbij' (s := D) (t := D' ×ˢ L.powerset)
    (f := fun S : Finset V => (S.card : ℚ))
    (g := fun TX : Finset ↥A × Finset V => (TX.1.card : ℚ) + (TX.2.card : ℚ))
    toProd fromProd h_maps_to h_maps_back h_left_inv h_right_inv h_sum_term

  have h_sum_eq : (∑ S ∈ D, (S.card : ℚ)) =
      (2 ^ L.card : ℚ) * (∑ T ∈ D', (T.card : ℚ)) + (D'.card : ℚ) * (L.card : ℚ) * (2 ^ L.card : ℚ) / 2 := by
    rw [h_sum_nbij, Finset.sum_product]
    have h1 : ∀ T ∈ D', (∑ X ∈ L.powerset, ((T.card : ℚ) + (X.card : ℚ))) =
        (2 ^ L.card : ℚ) * (T.card : ℚ) + (L.card : ℚ) * (2 ^ L.card : ℚ) / 2 := by
      intro T _
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_powerset,
        simple_graph_local_avg_dominating_order_eq_add_half_mul_of_leaf_neighbors_sum_powerset_card_rat]
      push_cast; ring
    have h2 : (∑ T ∈ D', ((2 ^ L.card : ℚ) * (T.card : ℚ) + (L.card : ℚ) * (2 ^ L.card : ℚ) / 2)) =
        (2 ^ L.card : ℚ) * (∑ T ∈ D', (T.card : ℚ)) + (D'.card : ℚ) * (L.card : ℚ) * (2 ^ L.card : ℚ) / 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl h1, h2]

  have hD'_ne : (D'.card : ℚ) ≠ 0 := by
    have huniv : (Finset.univ : Finset ↥A) ∈ D' := by
      rw [memD']
      simp
    have hpos : 0 < D'.card := Finset.card_pos.mpr ⟨Finset.univ, huniv⟩
    exact_mod_cast hpos.ne'

  have htwo_ne : (2 ^ L.card : ℚ) ≠ 0 := by positivity

  have hG : simple_graph_local_avg_dominating_order G v = (∑ S ∈ D, (S.card : ℚ)) / (D.card : ℚ) := by
    rw [simple_graph_local_avg_dominating_order, ← hD]
  have hH : simple_graph_local_avg_dominating_order H ⟨v, hv⟩ =
      (∑ T ∈ D', (T.card : ℚ)) / (D'.card : ℚ) := by
    rw [simple_graph_local_avg_dominating_order, ← hD']

  rw [hG, hH, h_sum_eq, h_card_eq]
  push_cast
  have : (D'.card : ℚ) * (2 ^ L.card : ℚ) ≠ 0 := mul_ne_zero hD'_ne htwo_ne
  field_simp
  ring
