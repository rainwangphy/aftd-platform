import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree

/-!
# simple_graph_eight_regular_triangle_degree_le_twenty_four

Topic: graphs   Node: 499184bb38fc

Provenance: helper lemma. step towards regular_eight_triangle_distinct_witness

In any 8-regular triangle-distinct graph, the triangle-degree of every vertex is at most 24.
-/

/-- The number of edges inside a finset `A`, counted as the 2-element subsets of `A` that are edges. -/
def simple_graph_eight_regular_triangle_degree_le_twenty_four_ec {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : ℕ :=
  ((A.powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)).card

/-- The edge count of the neighbourhood of a vertex is its triangle-degree. -/
lemma simple_graph_eight_regular_triangle_degree_le_twenty_four_ec_neighbor {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    simple_graph_eight_regular_triangle_degree_le_twenty_four_ec G (G.neighborFinset v)
      = simple_graph_triangle_degree G v := rfl

/-- Adding a vertex adjacent to every element of `A` adds `A.card` edges inside the set. -/
lemma simple_graph_eight_regular_triangle_degree_le_twenty_four_ec_insert {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (c : V) (hc : c ∉ A) (hadj : ∀ y ∈ A, G.Adj c y) :
    simple_graph_eight_regular_triangle_degree_le_twenty_four_ec G (insert c A)
      = simple_graph_eight_regular_triangle_degree_le_twenty_four_ec G A + A.card := by
  classical
  have hpair : ∀ y ∈ A, ∀ x ∈ ({c, y} : Finset V), ∀ z ∈ ({c, y} : Finset V), x ≠ z → G.Adj x z := by
    intro y hyA x hx z hz hne
    have hxA : x = c ∨ x = y := by simpa using hx
    have hzA : z = c ∨ z = y := by simpa using hz
    rcases hxA with hx1 | hx1 <;> rcases hzA with hz1 | hz1
    · exact absurd (hx1.trans hz1.symm) hne
    · rw [hx1, hz1]; exact hadj y hyA
    · rw [hx1, hz1]; exact (hadj y hyA).symm
    · exact absurd (hx1.trans hz1.symm) hne
  have hset : ((insert c A).powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)
      = ((A.powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y))
        ∪ A.image (fun y => ({c, y} : Finset V)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨⟨hsub, hcard⟩, hp⟩
      by_cases hcs : c ∈ s
      · have herase : (s.erase c).card = 1 := by rw [Finset.card_erase_of_mem hcs, hcard]
        obtain ⟨y, hy⟩ := Finset.card_eq_one.mp herase
        have hys : y ∈ s.erase c := by rw [hy]; exact Finset.mem_singleton_self y
        rw [Finset.mem_erase] at hys
        have hyA : y ∈ A := by
          have h1 : y ∈ insert c A := hsub hys.2
          rw [Finset.mem_insert] at h1
          rcases h1 with h | h
          · exact absurd h hys.1
          · exact h
        refine Or.inr ⟨y, hyA, ?_⟩
        show ({c, y} : Finset V) = s
        rw [← hy]
        exact Finset.insert_erase hcs
      · refine Or.inl ⟨⟨?_, hcard⟩, hp⟩
        intro z hz
        have h1 : z ∈ insert c A := hsub hz
        rw [Finset.mem_insert] at h1
        rcases h1 with h | h
        · exact absurd (h ▸ hz) hcs
        · exact h
    · rintro (⟨⟨hsub, hcard⟩, hp⟩ | ⟨y, hyA, rfl⟩)
      · exact ⟨⟨fun z hz => Finset.mem_insert_of_mem (hsub hz), hcard⟩, hp⟩
      · refine ⟨⟨?_, ?_⟩, hpair y hyA⟩
        · intro z hz
          have hz' : z = c ∨ z = y := by simpa using hz
          rw [Finset.mem_insert]
          rcases hz' with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr hyA
        · rw [Finset.card_pair]
          intro h
          exact hc (h ▸ hyA)
  have hdisj : Disjoint ((A.powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y))
      (A.image (fun y => ({c, y} : Finset V))) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_image] at hs1 hs2
    obtain ⟨⟨hsub, -⟩, -⟩ := hs1
    obtain ⟨y, hyA, rfl⟩ := hs2
    exact hc (hsub (Finset.mem_insert_self c {y}))
  have hinj : Set.InjOn (fun y => ({c, y} : Finset V)) (↑A : Set V) := by
    intro y hy y' hy' heq
    have heq' : ({c, y} : Finset V) = {c, y'} := heq
    have h1 : y ∈ ({c, y'} : Finset V) := by rw [← heq']; simp
    rw [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h | h
    · exact absurd (h ▸ hy) hc
    · exact h
  simp only [simple_graph_eight_regular_triangle_degree_le_twenty_four_ec]
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]

/-- In any 8-regular triangle-distinct graph, the triangle-degree of every vertex is at most 24. -/
theorem simple_graph_eight_regular_triangle_degree_le_twenty_four {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 8) (htd : simple_graph_is_triangle_distinct G) (v : V) :
    simple_graph_triangle_degree G v ≤ 24 := by
  classical
  by_contra hcon
  have hcon25 : 25 ≤ simple_graph_triangle_degree G v := by
    have h := not_le.mp hcon
    omega
  set A := G.neighborFinset v with hA
  have hvA : v ∉ A := by
    rw [hA, SimpleGraph.mem_neighborFinset]
    exact G.irrefl
  have hAcard : A.card = 8 := by
    rw [hA, G.card_neighborFinset_eq_degree, hreg v]
  have htdv : simple_graph_eight_regular_triangle_degree_le_twenty_four_ec G A
      = simple_graph_triangle_degree G v := by
    rw [hA]; exact simple_graph_eight_regular_triangle_degree_le_twenty_four_ec_neighbor G v
  set bad := (A.powersetCard 2).filter (fun s => ¬ (∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)) with hbad
  have hsplit : ((A.powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)).card
      + bad.card = (A.powersetCard 2).card := by
    rw [hbad]
    exact Finset.card_filter_add_card_filter_not _
  have hpow : (A.powersetCard 2).card = 28 := by
    rw [Finset.card_powersetCard, hAcard]; decide
  have hge : 25 ≤ ((A.powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)).card := by
    have h1 : ((A.powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)).card
        = simple_graph_eight_regular_triangle_degree_le_twenty_four_ec G A := rfl
    rw [h1, htdv]
    omega
  have hbadle : bad.card ≤ 3 := by omega
  set covered := bad.biUnion (fun s => s) with hcovdef
  have hmembad : ∀ s ∈ bad, s.card = 2 := by
    intro s hs
    rw [hbad] at hs
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1).2
  have hcovcard : covered.card ≤ 2 * bad.card := by
    have h1 : covered.card ≤ ∑ s ∈ bad, s.card := by
      rw [hcovdef]
      exact Finset.card_biUnion_le
    have h2 : ∑ s ∈ bad, s.card = ∑ s ∈ bad, (2 : ℕ) :=
      Finset.sum_congr rfl (fun s hs => hmembad s hs)
    have h3 : ∑ s ∈ bad, (2 : ℕ) = 2 * bad.card := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      omega
    omega
  have hlt : covered.card < A.card := by omega
  obtain ⟨c, hcA, hccov⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have huniv : ∀ y ∈ A, y ≠ c → G.Adj c y := by
    intro y hyA hyc
    by_contra hnc
    have hpair : ({c, y} : Finset V) ∈ bad := by
      rw [hbad, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro z hz
        have hz' : z = c ∨ z = y := by simpa using hz
        rcases hz' with rfl | rfl
        · exact hcA
        · exact hyA
      · rw [Finset.card_pair]; exact Ne.symm hyc
      · intro he
        exact hnc (he c (by simp) y (by simp) (Ne.symm hyc))
    have hmem : c ∈ covered := by
      rw [hcovdef, Finset.mem_biUnion]
      exact ⟨_, hpair, by simp⟩
    exact hccov hmem
  have hvc : G.Adj v c := by
    have h1 : c ∈ G.neighborFinset v := by rw [← hA]; exact hcA
    rwa [SimpleGraph.mem_neighborFinset] at h1
  have hvAerase : v ∉ A.erase c := by
    rw [Finset.mem_erase]
    exact fun h => hvA h.2
  have hNc : G.neighborFinset c = insert v (A.erase c) := by
    symm
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · rw [SimpleGraph.mem_neighborFinset]; exact hvc.symm
      · rw [Finset.mem_erase] at hz
        rw [SimpleGraph.mem_neighborFinset]
        exact huniv z hz.2 hz.1
    · have h2 : (insert v (A.erase c)).card = 8 := by
        rw [Finset.card_insert_of_notMem hvAerase, Finset.card_erase_of_mem hcA, hAcard]
      rw [G.card_neighborFinset_eq_degree, hreg c, h2]
  have stepA : simple_graph_eight_regular_triangle_degree_le_twenty_four_ec G A
      = simple_graph_eight_regular_triangle_degree_le_twenty_four_ec G (A.erase c) + (A.erase c).card := by
    conv_lhs => rw [← Finset.insert_erase hcA]
    exact simple_graph_eight_regular_triangle_degree_le_twenty_four_ec_insert G (A.erase c) c
      (Finset.notMem_erase c A)
      (fun y hy => huniv y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy))
  have stepC : simple_graph_eight_regular_triangle_degree_le_twenty_four_ec G (G.neighborFinset c)
      = simple_graph_eight_regular_triangle_degree_le_twenty_four_ec G (A.erase c) + (A.erase c).card := by
    rw [hNc]
    exact simple_graph_eight_regular_triangle_degree_le_twenty_four_ec_insert G (A.erase c) v hvAerase
      (fun y hy => by
        rw [Finset.mem_erase] at hy
        have h1 : y ∈ G.neighborFinset v := by rw [← hA]; exact hy.2
        rwa [SimpleGraph.mem_neighborFinset] at h1)
  have hfin : simple_graph_triangle_degree G c = simple_graph_triangle_degree G v := by
    rw [← simple_graph_eight_regular_triangle_degree_le_twenty_four_ec_neighbor G c, stepC, ← stepA, htdv]
  have hcv : c = v := htd hfin
  exact hvA (hcv ▸ hcA)
