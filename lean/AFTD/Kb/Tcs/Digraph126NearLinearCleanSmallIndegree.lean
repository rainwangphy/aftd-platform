import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_126_near_linear_clean_small_indegree

Topic: graphs   Node: 59cbd6ce6584

Provenance: helper lemma. Near-linear exceptional-vertex reduction for OP-110; at most 17 pair incidences can be repeated.

If a 7-outregular digraph on 126 vertices has at least 2629 common-predecessor edges, it has a vertex of indegree at most nine such that no pair involving it has two distinct common predecessors.
-/

private instance in478_clean126_decAdj (D : Digraph (Fin 126)) [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

lemma digraph_126_near_linear_clean_small_indegree_card_biUnion_lt_of_not_disjoint
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    {s : Finset ι} {f : ι → Finset α} {a b : ι} {u : α}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hua : u ∈ f a) (hub : u ∈ f b) :
    (s.biUnion f).card < ∑ x ∈ s, (f x).card := by
  have hnot : a ∉ s.erase a := by simp
  have hbiUnion : s.biUnion f = f a ∪ (s.erase a).biUnion f := by
    conv_lhs => rw [← Finset.insert_erase ha]
    rw [Finset.biUnion_insert]
  have hsum : ∑ x ∈ s, (f x).card = (f a).card + ∑ x ∈ s.erase a, (f x).card := by
    conv_lhs => rw [← Finset.insert_erase ha]
    rw [Finset.sum_insert hnot]
  have hu_inter : u ∈ f a ∩ (s.erase a).biUnion f := by
    rw [Finset.mem_inter]
    refine ⟨hua, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨b, ?_, hub⟩
    rw [Finset.mem_erase]
    exact ⟨hab.symm, hb⟩
  have hpos : 0 < (f a ∩ (s.erase a).biUnion f).card := Finset.card_pos.mpr ⟨u, hu_inter⟩
  have hcard_union := Finset.card_union_add_card_inter (f a) ((s.erase a).biUnion f)
  have hle : ((s.erase a).biUnion f).card ≤ ∑ x ∈ s.erase a, (f x).card := Finset.card_biUnion_le
  rw [hbiUnion] at *
  omega

lemma digraph_126_near_linear_clean_small_indegree_degree_lt_of_not_clean
    (D : Digraph (Fin 126)) [DecidableRel D.Adj]
    (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (v : Fin 126)
    (h_not_clean : ∃ u, u ≠ v ∧ ∃ a b, D.Adj a v ∧ D.Adj a u ∧ D.Adj b v ∧ D.Adj b u ∧ a ≠ b) :
    (digraph_common_predecessor_graph D).degree v <
      6 * (Finset.univ.filter fun w => D.Adj w v).card := by
  classical
  rcases h_not_clean with ⟨u, hune, a, b, hav, hau, hbv, hbu, hab⟩
  let ins : Finset (Fin 126) := Finset.univ.filter fun w => D.Adj w v
  let outs : Fin 126 → Finset (Fin 126) := fun w => (Finset.univ.filter fun z => D.Adj w z).erase v
  have ha_ins : a ∈ ins := by simp [ins, hav]
  have hb_ins : b ∈ ins := by simp [ins, hbv]
  have hu_a : u ∈ outs a := by
    simp only [outs, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hune, hau⟩
  have hu_b : u ∈ outs b := by
    simp only [outs, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hune, hbu⟩
  have hcover : (digraph_common_predecessor_graph D).neighborFinset v ⊆ ins.biUnion outs := by
    intro w hw
    have hw' := (SimpleGraph.mem_neighborFinset _ _ _).mp hw
    obtain ⟨hne, z, hzv, hzw⟩ := hw'
    apply Finset.mem_biUnion.mpr
    refine ⟨z, ?_, ?_⟩
    · simp [ins, hzv]
    · simp only [outs, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hne.symm, hzw⟩
  have hsize : ∀ w ∈ ins, (outs w).card = 6 := by
    intro w hw
    have hwv : D.Adj w v := (Finset.mem_filter.mp hw).2
    have he := Finset.card_erase_add_one (s := Finset.univ.filter fun z => D.Adj w z) (a := v) (by simp [hwv])
    have hd := hreg w
    change (outs w).card + 1 = _ at he
    omega
  have hlt := digraph_126_near_linear_clean_small_indegree_card_biUnion_lt_of_not_disjoint ha_ins hb_ins hab hu_a hu_b
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have h_sum : ∑ x ∈ ins, (outs x).card = 6 * ins.card := by
    calc
      ∑ x ∈ ins, (outs x).card = ∑ _x ∈ ins, 6 := Finset.sum_congr rfl hsize
      _ = 6 * ins.card := by simp [Nat.mul_comm]
  rw [h_sum] at hlt
  have hcard_le := Finset.card_le_card hcover
  change _ < 6 * ins.card
  omega

lemma digraph_126_near_linear_clean_small_indegree_degree_le_six_indegree
    (D : Digraph (Fin 126)) [DecidableRel D.Adj]
    (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = 7) (v : Fin 126) :
    (digraph_common_predecessor_graph D).degree v ≤ 6 * (Finset.univ.filter fun w => D.Adj w v).card := by
  classical
  let ins : Finset (Fin 126) := Finset.univ.filter fun w => D.Adj w v
  let outs : Fin 126 → Finset (Fin 126) := fun w => (Finset.univ.filter fun z => D.Adj w z).erase v
  have hcover : (digraph_common_predecessor_graph D).neighborFinset v ⊆ ins.biUnion outs := by
    intro u hu
    have hu' := (SimpleGraph.mem_neighborFinset _ _ _).mp hu
    obtain ⟨hne, w, hwv, hwu⟩ := hu'
    apply Finset.mem_biUnion.mpr
    refine ⟨w, ?_, ?_⟩
    · simp [ins, hwv]
    · simp only [outs, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hne.symm, hwu⟩
  have hsize : ∀ w ∈ ins, (outs w).card = 6 := by
    intro w hw
    have hwv : D.Adj w v := (Finset.mem_filter.mp hw).2
    have he := Finset.card_erase_add_one (s := Finset.univ.filter fun z => D.Adj w z) (a := v) (by simp [hwv])
    have hd := hreg w
    change (outs w).card + 1 = _ at he
    omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc
    _ ≤ (ins.biUnion outs).card := Finset.card_le_card hcover
    _ ≤ ∑ w ∈ ins, (outs w).card := Finset.card_biUnion_le
    _ = ∑ _w ∈ ins, 6 := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hsize w hw
    _ = 6 * ins.card := by simp [Nat.mul_comm]
    _ = 6 * (Finset.univ.filter fun w => D.Adj w v).card := rfl

lemma digraph_126_near_linear_clean_small_indegree_sum_indegree
    (D : Digraph (Fin 126)) [DecidableRel D.Adj]
    (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = 7) :
    ∑ v : Fin 126, (Finset.univ.filter fun w => D.Adj w v).card = 882 := by
  have h1 : ∑ v : Fin 126, (Finset.univ.filter fun w => D.Adj w v).card =
      ∑ v : Fin 126, (Finset.univ.filter fun w => D.Adj v w).card := by
    have h1a : ∑ v : Fin 126, (Finset.univ.filter fun w => D.Adj w v).card =
        ∑ v : Fin 126, ∑ w : Fin 126, if D.Adj w v then 1 else 0 := by
      apply Finset.sum_congr rfl; intro v _
      exact Finset.card_filter _ _
    have h1b : ∑ v : Fin 126, (Finset.univ.filter fun w => D.Adj v w).card =
        ∑ v : Fin 126, ∑ w : Fin 126, if D.Adj v w then 1 else 0 := by
      apply Finset.sum_congr rfl; intro v _
      exact Finset.card_filter _ _
    rw [h1a, h1b, Finset.sum_comm]
  rw [h1]
  simp [hreg]

theorem digraph_126_near_linear_clean_small_indegree
    (D : Digraph (Fin 126)) [DecidableRel D.Adj]
    (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (hedges : 2629 ≤ (digraph_common_predecessor_graph D).edgeFinset.card) :
    ∃ v, (Finset.univ.filter fun w => D.Adj w v).card ≤ 9 ∧
      ∀ u, u ≠ v → ∀ a b,
        D.Adj a v → D.Adj a u → D.Adj b v → D.Adj b u → a = b := by
  let G := digraph_common_predecessor_graph D
  let bad := Finset.univ.filter fun v => G.degree v < 6 * (Finset.univ.filter fun w => D.Adj w v).card
  have h_sum_in := digraph_126_near_linear_clean_small_indegree_sum_indegree D hreg
  have h_deg_le := digraph_126_near_linear_clean_small_indegree_degree_le_six_indegree D hreg
  have h_bad_card : bad.card ≤ 34 := by
    have hedgesG : 2629 ≤ G.edgeFinset.card := hedges
    let f : Fin 126 → ℕ := fun v => 6 * (Finset.univ.filter fun w => D.Adj w v).card
    have h_le : ∀ v ∈ (Finset.univ : Finset (Fin 126)), G.degree v ≤ f v := by
      intro v _
      exact h_deg_le v
    have h_tsub := Finset.sum_tsub_distrib (Finset.univ : Finset (Fin 126)) h_le
    have h_sum_f : ∑ v : Fin 126, f v = 5292 := by
      change ∑ v : Fin 126, 6 * (Finset.univ.filter fun w => D.Adj w v).card = 5292
      rw [← Finset.mul_sum]
      rw [h_sum_in]
      rfl
    have h_sum_g : ∑ v : Fin 126, G.degree v = 2 * G.edgeFinset.card :=
      SimpleGraph.sum_degrees_eq_twice_card_edges G
    have h_tsub_bound : ∑ v : Fin 126, (f v - G.degree v) ≤ 34 := by
      rw [h_tsub, h_sum_f, h_sum_g]
      omega
    have h_bad_le : bad.card ≤ ∑ v ∈ bad, (f v - G.degree v) := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro v hv
      have hv' : G.degree v < f v := (Finset.mem_filter.mp hv).2
      omega
    have h_subset : bad ⊆ Finset.univ := Finset.filter_subset _ _
    have h_sum_sub : ∑ v ∈ bad, (f v - G.degree v) ≤ ∑ v ∈ (Finset.univ : Finset (Fin 126)), (f v - G.degree v) :=
      Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun _ _ _ => Nat.zero_le _)
    omega
  have h_clean_prop : ∀ v ∉ bad, ∀ u, u ≠ v → ∀ a b, D.Adj a v → D.Adj a u → D.Adj b v → D.Adj b u → a = b := by
    intro v hv
    have h_not_bad : ¬ (G.degree v < 6 * (Finset.univ.filter fun w => D.Adj w v).card) := by
      intro h_in
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_in⟩)
    by_contra h_neg
    push Not at h_neg
    have h_lt := digraph_126_near_linear_clean_small_indegree_degree_lt_of_not_clean D hreg v h_neg
    exact h_not_bad h_lt
  let clean := (Finset.univ : Finset (Fin 126)) \ bad
  have h_bad_sub : bad ∩ Finset.univ = bad := Finset.inter_univ bad
  have h_clean_card : 92 ≤ clean.card := by
    have : clean.card = 126 - (bad ∩ Finset.univ).card := by
      rw [Finset.card_sdiff]
      simp
    rw [h_bad_sub] at this
    omega
  by_contra h_all
  push Not at h_all
  have h_ge : ∀ v ∈ clean, 10 ≤ (Finset.univ.filter fun w => D.Adj w v).card := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    have hcp := h_clean_prop v hv.2
    have h_not := h_all v
    by_contra h_lt
    push Not at h_lt
    have h_le9 : (Finset.univ.filter fun w => D.Adj w v).card ≤ 9 := by omega
    have hex := h_not h_le9
    rcases hex with ⟨u, hune, a, b, hav, hau, hbv, hbu, hab⟩
    have := hcp u hune a b hav hau hbv hbu
    exact hab this
  have h_sum_clean : clean.card * 10 ≤ ∑ v ∈ clean, (Finset.univ.filter fun w => D.Adj w v).card := by
    have := Finset.sum_le_sum h_ge
    rw [Finset.sum_const] at this
    omega
  have h_clean_sub : clean ⊆ Finset.univ := Finset.sdiff_subset
  have h_sum_le_all : ∑ v ∈ clean, (Finset.univ.filter fun w => D.Adj w v).card ≤
      ∑ v ∈ (Finset.univ : Finset (Fin 126)), (Finset.univ.filter fun w => D.Adj w v).card :=
    Finset.sum_le_sum_of_subset_of_nonneg h_clean_sub (fun _ _ _ => Nat.zero_le _)
  rw [h_sum_in] at h_sum_le_all
  omega
