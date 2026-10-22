import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphComplRegularTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphTriangleDegreeCompl
import AFTD.Kb.Tcs.SimpleGraphSixRegularNoTriangleDegreeFourteen
import AFTD.Kb.Tcs.SimpleGraphTriangleDegreeLeChoose
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree

/-!
# simple_graph_eight_regular_not_card_fifteen

Topic: graphs   Node: a110a46fa048

Provenance: helper lemma. step towards regular_eight_triangle_distinct_witness

No 8-regular triangle-distinct simple graph exists on 15 vertices.
-/

lemma simple_graph_eight_regular_not_card_fifteen_dup_of_fifteen {V : Type*}
    [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : H.IsRegularOfDegree 6) (v : V) (hv : simple_graph_triangle_degree H v = 15) :
    ∃ u : V, u ≠ v ∧ simple_graph_triangle_degree H u = 15 := by
  classical
  set A := H.neighborFinset v with hA
  have hvA : v ∉ A := by
    rw [hA, SimpleGraph.mem_neighborFinset]; exact H.irrefl
  have hAcard : A.card = 6 := by
    rw [hA, H.card_neighborFinset_eq_degree, hreg v]
  have hAadj : ∀ w ∈ A, H.Adj v w := by
    intro w hw
    have hmem : w ∈ H.neighborFinset v := by rw [← hA]; exact hw
    rwa [SimpleGraph.mem_neighborFinset] at hmem
  have hpowerset : (A.powersetCard 2).card = 15 := by
    rw [Finset.card_powersetCard, hAcard]; decide
  set good := (A.powersetCard 2).filter (fun t => ∀ a ∈ t, ∀ b ∈ t, a ≠ b → H.Adj a b) with hgood
  have hgoodcard : good.card = 15 := by rw [hgood, hA]; exact hv
  have hsubset : good ⊆ A.powersetCard 2 := Finset.filter_subset _ _
  have heq : good = A.powersetCard 2 := by
    refine Finset.eq_of_subset_of_card_le hsubset ?_
    rw [hpowerset, hgoodcard]
  have hclique : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → H.Adj a b := by
    intro a ha b hb hnab
    have hmem : ({a, b} : Finset V) ∈ good := by
      rw [heq, Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair hnab⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hb
    exact (Finset.mem_filter.mp hmem).2 a (by simp) b (by simp) hnab
  have hAnonempty : A.Nonempty := by rw [← Finset.card_pos, hAcard]; norm_num
  obtain ⟨u, huA⟩ := hAnonempty
  have hBcard : (H.neighborFinset u).card = 6 := by
    rw [H.card_neighborFinset_eq_degree, hreg u]
  have hBeq : H.neighborFinset u = insert v (A.erase u) := by
    have hsub : insert v (A.erase u) ⊆ H.neighborFinset u := by
      intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with hwv | hw
      · rw [hwv, SimpleGraph.mem_neighborFinset]; exact (hAadj u huA).symm
      · rw [Finset.mem_erase] at hw
        rw [SimpleGraph.mem_neighborFinset]
        exact hclique u huA w hw.2 (Ne.symm hw.1)
    have hinscard : (insert v (A.erase u)).card = 6 := by
      rw [Finset.card_insert_of_notMem, Finset.card_erase_of_mem huA, hAcard]
      rw [Finset.mem_erase]
      exact fun h => hvA h.2
    exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [hinscard, hBcard]))).symm
  have hBclique : ∀ a ∈ H.neighborFinset u, ∀ b ∈ H.neighborFinset u, a ≠ b → H.Adj a b := by
    intro a ha b hb hnab
    rw [hBeq] at ha hb
    rw [Finset.mem_insert] at ha hb
    rcases ha with hav | ha
    · rcases hb with hbv | hb
      · exact absurd (hav.trans hbv.symm) hnab
      · rw [Finset.mem_erase] at hb
        rw [hav]
        exact hAadj b hb.2
    · rw [Finset.mem_erase] at ha
      rcases hb with hbv | hb
      · rw [hbv]
        exact (hAadj a ha.2).symm
      · rw [Finset.mem_erase] at hb
        exact hclique a ha.2 b hb.2 hnab
  have htd_u : simple_graph_triangle_degree H u = 15 := by
    have htdform : simple_graph_triangle_degree H u =
        (((H.neighborFinset u).powersetCard 2).filter
          (fun t => ∀ a ∈ t, ∀ b ∈ t, a ≠ b → H.Adj a b)).card := rfl
    have hfilt : ((H.neighborFinset u).powersetCard 2).filter
        (fun t => ∀ a ∈ t, ∀ b ∈ t, a ≠ b → H.Adj a b) = (H.neighborFinset u).powersetCard 2 := by
      refine Finset.filter_true_of_mem ?_
      intro t ht
      rw [Finset.mem_powersetCard] at ht
      exact fun a ha b hb hnab => hBclique a (ht.1 ha) b (ht.1 hb) hnab
    rw [htdform, hfilt, Finset.card_powersetCard, hBcard]
    decide
  exact ⟨u, fun h => hvA (h ▸ huA), htd_u⟩

lemma simple_graph_eight_regular_not_card_fifteen_no_fifteen {V : Type*}
    [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : H.IsRegularOfDegree 6) (htd : simple_graph_is_triangle_distinct H) (v : V) :
    simple_graph_triangle_degree H v ≠ 15 := by
  intro hv
  obtain ⟨u, hne, hu⟩ := simple_graph_eight_regular_not_card_fifteen_dup_of_fifteen H hreg v hv
  exact hne (htd (hu.trans hv.symm))

/-- No 8-regular triangle-distinct simple graph exists on 15 vertices. -/
theorem simple_graph_eight_regular_not_card_fifteen {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hN : Fintype.card V = 15)
    (hreg : G.IsRegularOfDegree 8) (htd : simple_graph_is_triangle_distinct G) : False := by
  classical
  obtain ⟨hreg_c, htd_c⟩ := simple_graph_compl_regular_triangle_distinct G 8 15 hN hreg htd
  have hchoose : (6 : ℕ).choose 2 = 15 := by decide
  have hle : ∀ v : V, simple_graph_triangle_degree Gᶜ v ≤ 14 := by
    intro v
    have h1 : simple_graph_triangle_degree Gᶜ v ≤ (Gᶜ.degree v).choose 2 :=
      simple_graph_triangle_degree_le_choose Gᶜ v
    rw [hreg_c v, hchoose] at h1
    have h2 : simple_graph_triangle_degree Gᶜ v ≠ 15 :=
      simple_graph_eight_regular_not_card_fifteen_no_fifteen Gᶜ hreg_c htd_c v
    omega
  have hsubset : Finset.image (simple_graph_triangle_degree Gᶜ) (Finset.univ : Finset V) ⊆
      Finset.Icc 0 14 := by
    intro k hk
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hk
    obtain ⟨v, rfl⟩ := hk
    simp only [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, hle v⟩
  have himgcard : (Finset.image (simple_graph_triangle_degree Gᶜ) (Finset.univ : Finset V)).card = 15 := by
    rw [Finset.card_image_of_injective _ htd_c, Finset.card_univ, hN]
  have hIcc : (Finset.Icc 0 14 : Finset ℕ).card = 15 := by
    rw [Nat.card_Icc]
  have heq : Finset.image (simple_graph_triangle_degree Gᶜ) (Finset.univ : Finset V) = Finset.Icc 0 14 := by
    refine Finset.eq_of_subset_of_card_le hsubset ?_
    rw [hIcc, himgcard]
  have h14 : (14 : ℕ) ∈ Finset.image (simple_graph_triangle_degree Gᶜ) (Finset.univ : Finset V) := by
    rw [heq]; simp
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at h14
  obtain ⟨v, hv⟩ := h14
  exact simple_graph_six_regular_no_triangle_degree_fourteen Gᶜ hreg_c htd_c v hv
