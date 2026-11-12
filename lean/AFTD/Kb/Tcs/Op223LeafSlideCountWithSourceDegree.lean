import AFTD.Prelude

/-!
# op223_leaf_slide_count_with_source_degree

Topic: graphs   Node: fd1a96378aa1

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1; corrected auxiliary statement, experiment 23205

If a leaf v gains an edge to b while an edge from b to a vertex u of degree at least three is removed, with distinct u and v and no previous v-b edge, the number of leaves drops by exactly one.
-/

lemma op223_leaf_slide_count_with_source_degree_neighborSet_fromEdgeSet_singleton
    {V : Type*} [DecidableEq V] (x y z : V) (h : x ≠ y) :
    (SimpleGraph.fromEdgeSet {s(x, y)}).neighborSet z =
      if z = x then {y} else if z = y then {x} else ∅ := by
  ext w
  simp only [SimpleGraph.mem_neighborSet, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff]
  split_ifs with h1 h2 <;> aesop

lemma op223_leaf_slide_count_with_source_degree_neighborSet_slide
    {V : Type*} (X : SimpleGraph V) (u v b x : V) :
    (X.deleteEdges {s(u, b)} ⊔ SimpleGraph.fromEdgeSet {s(v, b)}).neighborSet x =
      (X.neighborSet x \ (SimpleGraph.fromEdgeSet {s(u, b)}).neighborSet x) ∪
        (SimpleGraph.fromEdgeSet {s(v, b)}).neighborSet x := by
  change ((X \ SimpleGraph.fromEdgeSet {s(u, b)}) ⊔ SimpleGraph.fromEdgeSet {s(v, b)}).neighborSet x = _
  rw [SimpleGraph.neighborSet_sup, SimpleGraph.neighborSet_sdiff]

lemma op223_leaf_slide_count_with_source_degree_neighborSet_slide_u
    {V : Type*} [DecidableEq V] (X : SimpleGraph V) (u v b : V)
    (huv : u ≠ v) (hbv : b ≠ v) (hub : X.Adj u b) :
    (X.deleteEdges {s(u, b)} ⊔ SimpleGraph.fromEdgeSet {s(v, b)}).neighborSet u =
      X.neighborSet u \ {b} := by
  have hub_ne : u ≠ b := X.ne_of_adj hub
  have hvb_ne : v ≠ b := hbv.symm
  rw [op223_leaf_slide_count_with_source_degree_neighborSet_slide,
      op223_leaf_slide_count_with_source_degree_neighborSet_fromEdgeSet_singleton u b u hub_ne,
      op223_leaf_slide_count_with_source_degree_neighborSet_fromEdgeSet_singleton v b u hvb_ne]
  simp [huv, hub_ne]

lemma op223_leaf_slide_count_with_source_degree_neighborSet_slide_v
    {V : Type*} [DecidableEq V] (X : SimpleGraph V) (u v b : V)
    (huv : u ≠ v) (hbv : b ≠ v) (hub : X.Adj u b) :
    (X.deleteEdges {s(u, b)} ⊔ SimpleGraph.fromEdgeSet {s(v, b)}).neighborSet v =
      X.neighborSet v ∪ {b} := by
  have hub_ne : u ≠ b := X.ne_of_adj hub
  have hvb_ne : v ≠ b := hbv.symm
  rw [op223_leaf_slide_count_with_source_degree_neighborSet_slide,
      op223_leaf_slide_count_with_source_degree_neighborSet_fromEdgeSet_singleton u b v hub_ne,
      op223_leaf_slide_count_with_source_degree_neighborSet_fromEdgeSet_singleton v b v hvb_ne]
  simp [huv.symm, hbv.symm]

lemma op223_leaf_slide_count_with_source_degree_neighborSet_slide_b
    {V : Type*} [DecidableEq V] (X : SimpleGraph V) (u v b : V)
    (hbv : b ≠ v) (hub : X.Adj u b) :
    (X.deleteEdges {s(u, b)} ⊔ SimpleGraph.fromEdgeSet {s(v, b)}).neighborSet b =
      (X.neighborSet b \ {u}) ∪ {v} := by
  have hub_ne : u ≠ b := X.ne_of_adj hub
  have hvb_ne : v ≠ b := hbv.symm
  rw [op223_leaf_slide_count_with_source_degree_neighborSet_slide,
      op223_leaf_slide_count_with_source_degree_neighborSet_fromEdgeSet_singleton u b b hub_ne,
      op223_leaf_slide_count_with_source_degree_neighborSet_fromEdgeSet_singleton v b b hvb_ne]
  simp [hub_ne.symm, hbv]

lemma op223_leaf_slide_count_with_source_degree_neighborSet_slide_other
    {V : Type*} [DecidableEq V] (X : SimpleGraph V) (u v b : V)
    (hbv : b ≠ v) (hub : X.Adj u b) {x : V} (hxu : x ≠ u) (hxv : x ≠ v) (hxb : x ≠ b) :
    (X.deleteEdges {s(u, b)} ⊔ SimpleGraph.fromEdgeSet {s(v, b)}).neighborSet x =
      X.neighborSet x := by
  have hub_ne : u ≠ b := X.ne_of_adj hub
  have hvb_ne : v ≠ b := hbv.symm
  rw [op223_leaf_slide_count_with_source_degree_neighborSet_slide,
      op223_leaf_slide_count_with_source_degree_neighborSet_fromEdgeSet_singleton u b x hub_ne,
      op223_leaf_slide_count_with_source_degree_neighborSet_fromEdgeSet_singleton v b x hvb_ne]
  simp [hxu, hxb, hxv]

theorem op223_leaf_slide_count_with_source_degree {V : Type*} [Fintype V] [DecidableEq V] (X : SimpleGraph V) (u v b : V) (huv : u ≠ v) (hbv : b ≠ v) (hub : X.Adj u b) (hvb : ¬ X.Adj v b) (hu : 3 ≤ Nat.card (X.neighborSet u)) (hv : Nat.card (X.neighborSet v) = 1) : (Finset.univ.filter (fun x : V => Nat.card ((X.deleteEdges {s(u, b)} ⊔ SimpleGraph.fromEdgeSet {s(v, b)}).neighborSet x) = 1)).card + 1 = (Finset.univ.filter (fun x : V => Nat.card (X.neighborSet x) = 1)).card := by
  let X' := X.deleteEdges {s(u, b)} ⊔ SimpleGraph.fromEdgeSet {s(v, b)}
  let s := Finset.univ.filter (fun x : V => Nat.card (X'.neighborSet x) = 1)
  let t := Finset.univ.filter (fun x : V => Nat.card (X.neighborSet x) = 1)
  have h_nv : X'.neighborSet v = X.neighborSet v ∪ {b} :=
    op223_leaf_slide_count_with_source_degree_neighborSet_slide_v X u v b huv hbv hub
  have h_nu : X'.neighborSet u = X.neighborSet u \ {b} :=
    op223_leaf_slide_count_with_source_degree_neighborSet_slide_u X u v b huv hbv hub
  have h_nb : X'.neighborSet b = (X.neighborSet b \ {u}) ∪ {v} :=
    op223_leaf_slide_count_with_source_degree_neighborSet_slide_b X u v b hbv hub
  have card_v : Nat.card (X'.neighborSet v) = 2 := by
    rw [Nat.card_coe_set_eq, h_nv, Set.union_singleton]
    have hb : b ∉ X.neighborSet v := hvb
    rw [Set.ncard_insert_of_notMem hb, ← Nat.card_coe_set_eq, hv]
  have hv_s : v ∉ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [card_v]
    decide
  have hv_t : v ∈ t := by
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, hv]
  have card_u : Nat.card (X'.neighborSet u) ≠ 1 := by
    rw [Nat.card_coe_set_eq, h_nu]
    have hb : b ∈ X.neighborSet u := hub
    have h_diff := Set.ncard_sdiff_singleton_add_one hb
    rw [Nat.card_coe_set_eq] at hu
    omega
  have card_b : Nat.card (X'.neighborSet b) = Nat.card (X.neighborSet b) := by
    rw [Nat.card_coe_set_eq, h_nb, Set.union_singleton]
    have hu_mem : u ∈ X.neighborSet b := hub.symm
    have hv_not : v ∉ X.neighborSet b \ {u} := fun h => hvb (h.1 : X.Adj b v).symm
    rw [Set.ncard_insert_of_notMem hv_not]
    have h_diff := Set.ncard_sdiff_singleton_add_one hu_mem
    rw [Nat.card_coe_set_eq]
    omega
  have h_iff : ∀ x ≠ v, x ∈ s ↔ x ∈ t := by
    intro x hx
    simp only [s, t, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hxu : x = u
    · subst hxu
      constructor
      · intro h1; exact (card_u h1).elim
      · intro h2; omega
    · by_cases hxb : x = b
      · subst hxb
        rw [card_b]
      · have h_oth := op223_leaf_slide_count_with_source_degree_neighborSet_slide_other X u v b hbv hub hxu hx hxb
        rw [h_oth]
  have ht : t = insert v s := by
    ext x
    by_cases hx : x = v
    · subst hx
      simp [hv_t]
    · simp [hx, (h_iff x hx).symm]
  change s.card + 1 = t.card
  rw [ht, Finset.card_insert_of_notMem hv_s]
