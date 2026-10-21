import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree

/-!
# simple_graph_six_regular_no_triangle_degree_fourteen

Topic: graphs   Node: 11fdc41e8a12

Provenance: helper lemma. step towards regular_eight_triangle_distinct_witness

In any 6-regular graph, no vertex has triangle-degree 14 if the graph is triangle-distinct.
-/

abbrev simple_graph_six_regular_no_triangle_degree_fourteen_ec {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ((S.powersetCard 2).filter (fun t => ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b)).card

lemma simple_graph_six_regular_no_triangle_degree_fourteen_ec_insert_raw {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (s : Finset V)
    (hx : x ∉ s) (hadj : ∀ y ∈ s, G.Adj x y) :
    (((insert x s).powersetCard 2).filter (fun t => ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b)).card
    = (((s.powersetCard 2).filter (fun t => ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b)).card) + s.card := by
  classical
  set p : Finset V → Prop := fun t => ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b with hp
  have hsplit : (insert x s).powersetCard 2
      = (s.powersetCard 2) ∪ ((s.powersetCard 1).image (insert x)) := by
    have h := Finset.powersetCard_succ_insert (x := x) (s := s) hx 1
    simpa using h
  have hdisj : Disjoint ((s.powersetCard 2).filter p) (((s.powersetCard 1).image (insert x)).filter p) := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_powersetCard] at ht1 ht2
    obtain ⟨⟨u, hu, rfl⟩, -⟩ := ht2
    exact hx (ht1.1.1 (Finset.mem_insert_self x u))
  have hBfilter : ((s.powersetCard 1).image (insert x)).filter p = (s.powersetCard 1).image (insert x) := by
    rw [Finset.filter_eq_self]
    intro t ht
    simp only [Finset.mem_image, Finset.mem_powersetCard] at ht
    obtain ⟨u, ⟨hus, hu1⟩, rfl⟩ := ht
    obtain ⟨y, hyu⟩ := Finset.card_eq_one.mp hu1
    rw [hyu] at hus ⊢
    intro a ha b hb hab
    rw [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · rw [ha, hb]; exact hadj y (hus (Finset.mem_singleton_self y))
    · rcases hb with hb | hb
      · rw [ha, hb]; exact (hadj y (hus (Finset.mem_singleton_self y))).symm
      · exact absurd (ha.trans hb.symm) hab
  have hinj : Set.InjOn (insert x) (↑(s.powersetCard 1) : Set (Finset V)) := by
    intro u hu v hv huv
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hu hv
    have hxu : x ∉ u := fun h => hx (hu.1 h)
    have hxv : x ∉ v := fun h => hx (hv.1 h)
    have hh := congrArg (fun w => w.erase x) huv
    simpa only [Finset.erase_insert hxu, Finset.erase_insert hxv] using hh
  have hBcard : (((s.powersetCard 1).image (insert x))).card = s.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_powersetCard, Nat.choose_one_right]
  rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj, hBfilter, hBcard]

lemma simple_graph_six_regular_no_triangle_degree_fourteen_ec_insert {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (s : Finset V)
    (hx : x ∉ s) (hadj : ∀ y ∈ s, G.Adj x y) :
    simple_graph_six_regular_no_triangle_degree_fourteen_ec G (insert x s)
      = simple_graph_six_regular_no_triangle_degree_fourteen_ec G s + s.card :=
  simple_graph_six_regular_no_triangle_degree_fourteen_ec_insert_raw G x s hx hadj

/-- In any 6-regular graph, no vertex has triangle-degree 14 if the graph is triangle-distinct: a neighborhood with 14 edges misses exactly one edge, leaving at least 4 neighbors with full neighborhood in N(v) and thus identical triangle-degree 14. -/
theorem simple_graph_six_regular_no_triangle_degree_fourteen {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : H.IsRegularOfDegree 6) (htd : simple_graph_is_triangle_distinct H) (v : V) :
    simple_graph_triangle_degree H v ≠ 14 := by
  classical
  intro h14
  set A := H.neighborFinset v with hA
  have hvA : v ∉ A := by
    rw [hA, SimpleGraph.mem_neighborFinset]; exact H.irrefl
  have hAcard : A.card = 6 := by
    rw [hA, H.card_neighborFinset_eq_degree, hreg v]
  have htdv : simple_graph_six_regular_no_triangle_degree_fourteen_ec H A = 14 := h14
  set bad := (A.powersetCard 2).filter (fun t => ¬ (∀ a ∈ t, ∀ b ∈ t, a ≠ b → H.Adj a b)) with hbad_def
  have hbadcard : bad.card = 1 := by
    have htot : ((A.powersetCard 2).filter (fun t => ∀ a ∈ t, ∀ b ∈ t, a ≠ b → H.Adj a b)).card
        + bad.card = (A.powersetCard 2).card := by
      simpa [hbad_def] using (Finset.card_filter_add_card_filter_not (s := A.powersetCard 2)
        (p := fun t => ∀ a ∈ t, ∀ b ∈ t, a ≠ b → H.Adj a b))
    have h1 : ((A.powersetCard 2).filter (fun t => ∀ a ∈ t, ∀ b ∈ t, a ≠ b → H.Adj a b)).card = 14 := htdv
    have h2 : (A.powersetCard 2).card = 15 := by
      rw [Finset.card_powersetCard, hAcard]; decide
    omega
  obtain ⟨s0, hs0⟩ := Finset.card_eq_one.mp hbadcard
  have hs0mem : s0 ∈ A.powersetCard 2 := by
    have h : s0 ∈ bad := by rw [hs0]; exact Finset.mem_singleton_self s0
    exact (Finset.mem_filter.mp h).1
  have hs0sub : s0 ⊆ A := (Finset.mem_powersetCard.mp hs0mem).1
  have hs0card : s0.card = 2 := (Finset.mem_powersetCard.mp hs0mem).2
  have hsdiff : (A \ s0).card = 4 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hs0sub, hAcard, hs0card]
  have hne : (A \ s0).Nonempty := by rw [← Finset.card_pos, hsdiff]; norm_num
  obtain ⟨c, hc⟩ := hne
  rw [Finset.mem_sdiff] at hc
  have hcgood : ∀ y ∈ A, y ≠ c → H.Adj c y := by
    intro y hyA hyne
    by_contra hnc
    have hpb : ({c, y} : Finset V) ∈ bad := by
      rw [hbad_def, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with hzc | hzy
          · rw [hzc]; exact hc.1
          · rw [hzy]; exact hyA
        · exact Finset.card_pair (Ne.symm hyne)
      · intro hcl
        exact hnc (hcl c (by simp) y (by simp) (Ne.symm hyne))
    have hceq : ({c, y} : Finset V) = s0 := by
      rw [hs0] at hpb; rwa [Finset.mem_singleton] at hpb
    exact hc.2 (hceq ▸ (by simp : c ∈ ({c, y} : Finset V)))
  have hvc : H.Adj v c := by
    have hmem : c ∈ H.neighborFinset v := by rw [← hA]; exact hc.1
    rwa [SimpleGraph.mem_neighborFinset] at hmem
  have hvAerase : v ∉ A.erase c := by
    rw [Finset.mem_erase]; intro h; exact hvA h.2
  have hNc : H.neighborFinset c = insert v (A.erase c) := by
    symm
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · rw [SimpleGraph.mem_neighborFinset]; exact hvc.symm
      · rw [Finset.mem_erase] at hy
        rw [SimpleGraph.mem_neighborFinset]
        exact hcgood y hy.2 hy.1
    · rw [H.card_neighborFinset_eq_degree, hreg c, Finset.card_insert_of_notMem hvAerase,
        Finset.card_erase_of_mem hc.1, hAcard]
  have step1 : simple_graph_six_regular_no_triangle_degree_fourteen_ec H (insert v (A.erase c))
      = simple_graph_six_regular_no_triangle_degree_fourteen_ec H (A.erase c) + (A.erase c).card := by
    apply simple_graph_six_regular_no_triangle_degree_fourteen_ec_insert
    · exact hvAerase
    · intro y hy
      rw [Finset.mem_erase] at hy
      have hya : y ∈ H.neighborFinset v := by rw [← hA]; exact hy.2
      rwa [SimpleGraph.mem_neighborFinset] at hya
  have step2 : simple_graph_six_regular_no_triangle_degree_fourteen_ec H A
      = simple_graph_six_regular_no_triangle_degree_fourteen_ec H (A.erase c) + (A.erase c).card := by
    conv_lhs => rw [← Finset.insert_erase hc.1]
    apply simple_graph_six_regular_no_triangle_degree_fourteen_ec_insert
    · exact Finset.notMem_erase c A
    · intro y hy
      rw [Finset.mem_erase] at hy
      exact hcgood y hy.2 hy.1
  have hcd14 : simple_graph_triangle_degree H c = 14 := by
    have hbridge : simple_graph_triangle_degree H c
        = simple_graph_six_regular_no_triangle_degree_fourteen_ec H (H.neighborFinset c) := rfl
    rw [hbridge, hNc, step1, ← step2]
    exact htdv
  have heq : simple_graph_triangle_degree H c = simple_graph_triangle_degree H v := by
    rw [hcd14, h14]
  have hcv : c = v := htd heq
  exact hvA (hcv ▸ hc.1)
