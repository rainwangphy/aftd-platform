import AFTD.Prelude

/-!
# graph_adjacent_twins_external_codegree_one_count

Topic: graphs   Node: 84c2970f2885

Provenance: helper lemma. OP-1957: averaged complement-codegree bound from adjacent twins; experiment 34838 checks the sharpness construction.

For adjacent complement twins and a common external nonneighbor set C, all but at most floor((d−1)(d−2)/2) vertices of C have complement codegree at most one with either twin.
-/

lemma graph_adjacent_twins_external_codegree_one_count_finset_sum_card_filter_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (R : α → β → Prop) [DecidableRel R] :
    ∑ a ∈ s, (t.filter (fun b => R a b)).card = ∑ b ∈ t, (s.filter (fun a => R a b)).card := by
  have h1 : (∑ a ∈ s, (t.filter (fun b => R a b)).card) = ∑ a ∈ s, ∑ b ∈ t, if R a b then 1 else 0 := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact Finset.card_filter (fun b => R a b) t
  have h2 : (∑ b ∈ t, (s.filter (fun a => R a b)).card) = ∑ b ∈ t, ∑ a ∈ s, if R a b then 1 else 0 := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact Finset.card_filter (fun a => R a b) s
  rw [h1, h2, Finset.sum_comm]

lemma graph_adjacent_twins_external_codegree_one_count_not_adj_y_of_mem_C
    {V : Type*} (H : SimpleGraph V) (x y : V)
    (htwins : ∀ w, w ≠ x → w ≠ y → (H.Adj x w ↔ H.Adj y w))
    (C : Finset V) (hx : x ∉ C) (hy : y ∉ C) (hcover : ∀ z ∈ C, ¬ H.Adj x z)
    {z : V} (hz : z ∈ C) : ¬ H.Adj y z := by
  have hzx : z ≠ x := by rintro rfl; exact hx hz
  have hzy : z ≠ y := by rintro rfl; exact hy hz
  have htw := htwins z hzx hzy
  have hxnz := hcover z hz
  intro hyz
  exact hxnz (htw.mpr hyz)

lemma graph_adjacent_twins_external_codegree_one_count_filter_adj_eq
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (htwins : ∀ w, w ≠ x → w ≠ y → (H.Adj x w ↔ H.Adj y w))
    (C : Finset V) (hx : x ∉ C) (hy : y ∉ C) (hcover : ∀ z ∈ C, ¬ H.Adj x z)
    (z : V) (hz : z ∈ C) :
    ((Finset.univ : Finset V).filter (fun w => H.Adj x w ∧ H.Adj z w)) =
    ((H.neighborFinset x).erase y).filter (fun w => H.Adj w z) := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨hxw, hzw⟩
    refine ⟨⟨fun h => ?_, hxw⟩, H.adj_symm hzw⟩
    have hyz : H.Adj y z := by rw [← h]; exact H.adj_symm hzw
    exact graph_adjacent_twins_external_codegree_one_count_not_adj_y_of_mem_C H x y htwins C hx hy hcover hz hyz
  · rintro ⟨⟨hwy, hxw⟩, hwz⟩
    exact ⟨hxw, H.adj_symm hwz⟩

lemma graph_adjacent_twins_external_codegree_one_count_card_S_le
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (d : ℕ) (hmax : ∀ w, H.degree w ≤ d)
    (x y : V) (hxy : H.Adj x y) :
    (((H.neighborFinset x).erase y).card) ≤ d - 1 := by
  have hy_mem : y ∈ H.neighborFinset x := by
    simp [SimpleGraph.mem_neighborFinset, hxy]
  rw [Finset.card_erase_of_mem hy_mem, SimpleGraph.card_neighborFinset_eq_degree]
  have := hmax x
  omega

lemma graph_adjacent_twins_external_codegree_one_count_card_neighbors_in_C_le
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (d : ℕ) (hmax : ∀ v, H.degree v ≤ d)
    (x y : V) (hxy : H.Adj x y)
    (htwins : ∀ v, v ≠ x → v ≠ y → (H.Adj x v ↔ H.Adj y v))
    (C : Finset V) (hx : x ∉ C) (hy : y ∉ C)
    (w : V) (hw : w ∈ (H.neighborFinset x).erase y) :
    (C.filter (fun z => H.Adj w z)).card ≤ d - 2 := by
  have hw_adj_x : H.Adj x w := by
    have := Finset.mem_of_mem_erase hw
    rwa [SimpleGraph.mem_neighborFinset] at this
  have hwx : w ≠ x := hw_adj_x.ne'
  have hwy : w ≠ y := Finset.ne_of_mem_erase hw
  have hw_adj_y : H.Adj y w := (htwins w hwx hwy).mp hw_adj_x
  have hx_in_w : x ∈ H.neighborFinset w := by
    simp [SimpleGraph.mem_neighborFinset, hw_adj_x.symm]
  have hy_in_w : y ∈ H.neighborFinset w := by
    simp [SimpleGraph.mem_neighborFinset, hw_adj_y.symm]
  have hxy_ne : x ≠ y := hxy.ne
  have hsub : C.filter (fun z => H.Adj w z) ⊆ (H.neighborFinset w \ {x, y}) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      not_or, SimpleGraph.mem_neighborFinset] at hz ⊢
    refine ⟨hz.2, ?_, ?_⟩
    · rintro rfl; exact hx hz.1
    · rintro rfl; exact hy hz.1
  have hpair_sub : ({x, y} : Finset V) ⊆ H.neighborFinset w := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx_in_w
    · exact hy_in_w
  have hcard_sdiff : (H.neighborFinset w \ {x, y}).card = (H.neighborFinset w).card - 2 := by
    rw [Finset.card_sdiff_of_subset hpair_sub, Finset.card_pair hxy_ne]
  have hle := Finset.card_le_card hsub
  rw [hcard_sdiff, SimpleGraph.card_neighborFinset_eq_degree] at hle
  have := hmax w
  omega

theorem graph_adjacent_twins_external_codegree_one_count
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (d : ℕ) (hd : 2 ≤ d) (hmax : ∀ w, H.degree w ≤ d)
    (x y : V) (hxy : H.Adj x y)
    (htwins : ∀ w, w ≠ x → w ≠ y → (H.Adj x w ↔ H.Adj y w))
    (C : Finset V) (hx : x ∉ C) (hy : y ∉ C)
    (hcover : ∀ z ∈ C, ¬ H.Adj x z)
 :
    C.card ≤ (C.filter (fun z =>
      ((Finset.univ : Finset V).filter (fun w => H.Adj x w ∧ H.Adj z w)).card ≤ 1)).card +
      ((d-1)*(d-2))/2 := by
  have _ := hd
  let Good := C.filter (fun z =>
    ((Finset.univ : Finset V).filter (fun w => H.Adj x w ∧ H.Adj z w)).card ≤ 1)
  let Bad := C.filter (fun z =>
    ¬ (((Finset.univ : Finset V).filter (fun w => H.Adj x w ∧ H.Adj z w)).card ≤ 1))
  have hC_eq : C.card = Good.card + Bad.card := by
    exact (Finset.card_filter_add_card_filter_not _).symm
  let S := (H.neighborFinset x).erase y
  have h_sum_le : ∑ w ∈ S, (Bad.filter (fun z => H.Adj w z)).card ≤ (d - 1) * (d - 2) := by
    have h1 : ∑ w ∈ S, (Bad.filter (fun z => H.Adj w z)).card ≤ ∑ w ∈ S, (d - 2) := by
      apply Finset.sum_le_sum
      intro w hw
      have hsub : Bad.filter (fun z => H.Adj w z) ⊆ C.filter (fun z => H.Adj w z) := by
        intro z hz
        simp only [Finset.mem_filter] at hz ⊢
        exact ⟨Finset.mem_of_mem_filter z hz.1, hz.2⟩
      exact (Finset.card_le_card hsub).trans
        (graph_adjacent_twins_external_codegree_one_count_card_neighbors_in_C_le H d hmax x y hxy htwins C hx hy w hw)
    have h2 : ∑ w ∈ S, (d - 2) = S.card * (d - 2) := by simp
    have h3 : S.card * (d - 2) ≤ (d - 1) * (d - 2) :=
      Nat.mul_le_mul_right (d - 2) (graph_adjacent_twins_external_codegree_one_count_card_S_le H d hmax x y hxy)
    omega
  have h_sum_ge : 2 * Bad.card ≤ ∑ z ∈ Bad, (S.filter (fun w => H.Adj w z)).card := by
    have h_each : ∀ z ∈ Bad, 2 ≤ (S.filter (fun w => H.Adj w z)).card := by
      intro z hz
      have hzC : z ∈ C := Finset.mem_of_mem_filter z hz
      have h_not_le : ¬ (((Finset.univ : Finset V).filter (fun w => H.Adj x w ∧ H.Adj z w)).card ≤ 1) :=
        (Finset.mem_filter.mp hz).2
      have h_eq : ((Finset.univ : Finset V).filter (fun w => H.Adj x w ∧ H.Adj z w)) =
          S.filter (fun w => H.Adj w z) :=
        graph_adjacent_twins_external_codegree_one_count_filter_adj_eq H x y htwins C hx hy hcover z hzC
      rw [h_eq] at h_not_le
      omega
    have h_sum : ∑ z ∈ Bad, 2 ≤ ∑ z ∈ Bad, (S.filter (fun w => H.Adj w z)).card :=
      Finset.sum_le_sum (fun z hz => h_each z hz)
    have : ∑ z ∈ Bad, 2 = 2 * Bad.card := by simp [mul_comm]
    rwa [this] at h_sum
  have h_double_count : ∑ w ∈ S, (Bad.filter (fun z => H.Adj w z)).card =
      ∑ z ∈ Bad, (S.filter (fun w => H.Adj w z)).card :=
    graph_adjacent_twins_external_codegree_one_count_finset_sum_card_filter_eq S Bad H.Adj
  have h_bad_le : 2 * Bad.card ≤ (d - 1) * (d - 2) := by
    omega
  change C.card ≤ Good.card + ((d - 1) * (d - 2)) / 2
  omega
