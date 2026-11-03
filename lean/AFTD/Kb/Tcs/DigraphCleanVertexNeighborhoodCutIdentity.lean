import AFTD.Prelude

/-!
# digraph_clean_vertex_neighborhood_cut_identity

Topic: graphs   Node: 0aea6297e1a3

Provenance: helper lemma. Clean-vertex reduction for the minimum-counterexample campaign route to OP-110.

For a clean vertex of a loopless oriented r-outregular arc-dominated digraph, if S and O are its in- and out-neighborhoods, the number of arcs from S outside S∪O∪{v} plus 2|S|+r equals r|S|.
-/

open Finset

private lemma digraph_clean_vertex_neighborhood_cut_identity_sum_card_filter_comm
    {α : Type*} [DecidableEq α] (S T : Finset α) (P : α → α → Prop) [DecidableRel P] :
    ∑ x ∈ S, (T.filter (P x)).card = ∑ y ∈ T, (S.filter (fun x => P x y)).card := by
  simp_rw [card_filter]
  rw [sum_comm]

private lemma digraph_clean_vertex_neighborhood_cut_identity_filter_singleton
    {α : Type*} [DecidableEq α] {D : Digraph α} [DecidableRel D.Adj] {x v : α} (h : D.Adj x v) :
    (({v} : Finset α).filter (fun w => D.Adj x w)).card = 1 := by
  have : ({v} : Finset α).filter (fun w => D.Adj x w) = {v} := by
    ext a
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨rfl, _⟩; rfl
    · rintro rfl; exact ⟨rfl, h⟩
  rw [this, card_singleton]

private lemma digraph_clean_vertex_neighborhood_cut_identity_in_degree_S
    {α : Type*} [Fintype α] [DecidableEq α] {D : Digraph α} [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v)
    (v : α)
    (hclean : ∀ u, u ≠ v → ∀ a b,
      D.Adj a v → D.Adj a u → D.Adj b v → D.Adj b u → a = b)
    (S : Finset α)
    (hS : S = Finset.univ.filter fun w => D.Adj w v)
    (y : α) (hy : y ∈ S) :
    (S.filter (fun x => D.Adj x y)).card = 1 := by
  rw [hS, mem_filter] at hy
  have hyv : D.Adj y v := hy.2
  have hyne : y ≠ v := by
    rintro rfl
    exact hloop _ hyv
  obtain ⟨w, hwy, hwv⟩ := hdom y v hyv
  have hw_mem : w ∈ S.filter (fun x => D.Adj x y) := by
    rw [mem_filter, hS, mem_filter]
    exact ⟨⟨mem_univ w, hwv⟩, hwy⟩
  have h_uniq : ∀ a ∈ S.filter (fun x => D.Adj x y),
                ∀ b ∈ S.filter (fun x => D.Adj x y), a = b := by
    intro a ha b hb
    rw [mem_filter, hS, mem_filter] at ha hb
    exact hclean y hyne a b ha.1.2 ha.2 hb.1.2 hb.2
  exact card_eq_one.2 ⟨w, by
    ext z
    constructor
    · intro hz
      have := h_uniq z hz w hw_mem
      exact mem_singleton.2 this
    · intro hz
      rw [mem_singleton.1 hz]
      exact hw_mem⟩

private lemma digraph_clean_vertex_neighborhood_cut_identity_in_degree_O
    {α : Type*} [Fintype α] [DecidableEq α] {D : Digraph α} [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v)
    (v : α)
    (hclean : ∀ u, u ≠ v → ∀ a b,
      D.Adj a v → D.Adj a u → D.Adj b v → D.Adj b u → a = b)
    (S O : Finset α)
    (hS : S = Finset.univ.filter fun w => D.Adj w v)
    (hO : O = Finset.univ.filter fun w => D.Adj v w)
    (u : α) (hu : u ∈ O) :
    (S.filter (fun x => D.Adj x u)).card = 1 := by
  rw [hO, mem_filter] at hu
  have hvu : D.Adj v u := hu.2
  have hune : u ≠ v := by
    rintro rfl
    exact hloop _ hvu
  obtain ⟨w, hwv, hwu⟩ := hdom v u hvu
  have hw_mem : w ∈ S.filter (fun x => D.Adj x u) := by
    rw [mem_filter, hS, mem_filter]
    exact ⟨⟨mem_univ w, hwv⟩, hwu⟩
  have h_uniq : ∀ a ∈ S.filter (fun x => D.Adj x u),
                ∀ b ∈ S.filter (fun x => D.Adj x u), a = b := by
    intro a ha b hb
    rw [mem_filter, hS, mem_filter] at ha hb
    exact hclean u hune a b ha.1.2 ha.2 hb.1.2 hb.2
  exact card_eq_one.2 ⟨w, by
    ext z
    constructor
    · intro hz
      have := h_uniq z hz w hw_mem
      exact mem_singleton.2 this
    · intro hz
      rw [mem_singleton.1 hz]
      exact hw_mem⟩

private lemma digraph_clean_vertex_neighborhood_cut_identity_partition
    {α : Type*} [Fintype α] [DecidableEq α] {D : Digraph α} [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (v : α) (S O : Finset α)
    (hS : S = Finset.univ.filter fun w => D.Adj w v)
    (hO : O = Finset.univ.filter fun w => D.Adj v w)
    (p : α → Prop) [DecidablePred p] :
    (univ.filter p).card =
      ((univ \ (S ∪ O ∪ {v})).filter p).card +
      (S.filter p).card + (O.filter p).card + (({v} : Finset α).filter p).card := by
  have hvS : v ∉ S := by
    rw [hS, mem_filter]; rintro ⟨-, h⟩; exact hloop _ h
  have hvO : v ∉ O := by
    rw [hO, mem_filter]; rintro ⟨-, h⟩; exact hloop _ h
  have hdisj_SO : Disjoint S O := by
    rw [disjoint_iff_ne]
    intro a ha b hb hab
    subst hab
    rw [hS, mem_filter] at ha
    rw [hO, mem_filter] at hb
    exact hori a v ha.2 hb.2
  have hdisj_SO_v : Disjoint (S ∪ O) {v} := by
    rw [disjoint_singleton_right, mem_union, not_or]
    exact ⟨hvS, hvO⟩
  set K := S ∪ O ∪ {v} with hK
  have h_univ : (univ \ K) ∪ K = univ := sdiff_union_of_subset (subset_univ K)
  have h_disj_sdiff : Disjoint (univ \ K) K := disjoint_sdiff_self_left
  have h1 : (univ.filter p).card = ((univ \ K).filter p).card + (K.filter p).card := by
    conv_lhs => rw [← h_univ]
    rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h_disj_sdiff)]
  have h2 : (K.filter p).card = ((S ∪ O).filter p).card + (({v} : Finset α).filter p).card := by
    change (((S ∪ O) ∪ {v}).filter p).card = _
    rw [filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj_SO_v)]
  have h3 : ((S ∪ O).filter p).card = (S.filter p).card + (O.filter p).card := by
    rw [filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj_SO)]
  omega

theorem digraph_clean_vertex_neighborhood_cut_identity
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (r : ℕ) (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = r)
    (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v)
    (v : α)
    (hclean : ∀ u, u ≠ v → ∀ a b,
      D.Adj a v → D.Adj a u → D.Adj b v → D.Adj b u → a = b)
    (S O : Finset α)
    (hS : S = Finset.univ.filter fun w => D.Adj w v)
    (hO : O = Finset.univ.filter fun w => D.Adj v w) :
    (∑ x ∈ S, ((Finset.univ \ (S ∪ O ∪ {v})).filter fun w => D.Adj x w).card) +
      2 * S.card + r = r * S.card := by
  have h_split : ∀ x ∈ S,
      r = ((Finset.univ \ (S ∪ O ∪ {v})).filter (fun w => D.Adj x w)).card +
          (S.filter (fun w => D.Adj x w)).card +
          (O.filter (fun w => D.Adj x w)).card + 1 := by
    intro x hx
    have hxv : D.Adj x v := by
      rw [hS, mem_filter] at hx
      exact hx.2
    rw [← hreg x]
    rw [digraph_clean_vertex_neighborhood_cut_identity_partition hloop hori v S O hS hO]
    rw [digraph_clean_vertex_neighborhood_cut_identity_filter_singleton hxv]
  have h_sum_split : ∑ x ∈ S, r =
      (∑ x ∈ S, ((Finset.univ \ (S ∪ O ∪ {v})).filter (fun w => D.Adj x w)).card) +
      (∑ x ∈ S, (S.filter (fun w => D.Adj x w)).card) +
      (∑ x ∈ S, (O.filter (fun w => D.Adj x w)).card) +
      S.card := by
    have h_eq : ∑ x ∈ S, r = ∑ x ∈ S,
        (((Finset.univ \ (S ∪ O ∪ {v})).filter (fun w => D.Adj x w)).card +
         (S.filter (fun w => D.Adj x w)).card +
         (O.filter (fun w => D.Adj x w)).card + 1) :=
      sum_congr rfl h_split
    rw [h_eq]
    simp only [sum_add_distrib]
    rw [← card_eq_sum_ones]
  have h_sum_S : ∑ x ∈ S, (S.filter (fun w => D.Adj x w)).card = S.card := by
    rw [digraph_clean_vertex_neighborhood_cut_identity_sum_card_filter_comm]
    have : ∑ y ∈ S, (S.filter (fun x => D.Adj x y)).card = ∑ y ∈ S, 1 :=
      sum_congr rfl (digraph_clean_vertex_neighborhood_cut_identity_in_degree_S hloop hdom v hclean S hS)
    rw [this, ← card_eq_sum_ones]
  have h_sum_O : ∑ x ∈ S, (O.filter (fun w => D.Adj x w)).card = r := by
    rw [digraph_clean_vertex_neighborhood_cut_identity_sum_card_filter_comm]
    have : ∑ u ∈ O, (S.filter (fun x => D.Adj x u)).card = ∑ u ∈ O, 1 :=
      sum_congr rfl (digraph_clean_vertex_neighborhood_cut_identity_in_degree_O hloop hdom v hclean S O hS hO)
    rw [this, ← card_eq_sum_ones]
    rw [hO, hreg v]
  have h_sum_r : ∑ x ∈ S, r = S.card * r := sum_const_nat (fun _ _ => rfl)
  rw [mul_comm] at h_sum_r
  omega
