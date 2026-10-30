import AFTD.Prelude
import AFTD.Kb.Tcs.IcosahedronGraph
import AFTD.Kb.Tcs.IsAmplyRegular

/-!
# icosahedron_is_amply_regular

Topic: graphs   Node: 957d68e1aaea

Provenance: helper lemma. arXiv:2610.36620, Proof of Theorem 3.6

The icosahedron graph on Fin 12 is an amply regular graph with parameters (5, 2, 2) and its diameter is 3.
-/

abbrev icosahedron_is_amply_regular_rel (x y : ℕ) : Prop :=
  (x = 0 ∧ 1 ≤ y ∧ y ≤ 5) ∨
  (x = 11 ∧ 6 ≤ y ∧ y ≤ 10) ∨
  (1 ≤ x ∧ x ≤ 5 ∧ 1 ≤ y ∧ y ≤ 5 ∧ (y = x % 5 + 1 ∨ x = y % 5 + 1)) ∨
  (6 ≤ x ∧ x ≤ 10 ∧ 6 ≤ y ∧ y ≤ 10 ∧ (y = 6 + (x - 6 + 1) % 5 ∨ x = 6 + (y - 6 + 1) % 5)) ∨
  (1 ≤ x ∧ x ≤ 5 ∧ 6 ≤ y ∧ y ≤ 10 ∧ (y = 6 + (x - 1) ∨ y = 6 + (x - 1 + 4) % 5))

def icosahedron_is_amply_regular_adj (u v : Fin 12) : Bool :=
  decide (u ≠ v ∧ (icosahedron_is_amply_regular_rel u.val v.val ∨
    icosahedron_is_amply_regular_rel v.val u.val))

def icosahedron_is_amply_regular_nbr (v : Fin 12) : Finset (Fin 12) :=
  Finset.univ.filter (fun w => icosahedron_is_amply_regular_adj v w)

lemma icosahedron_is_amply_regular_adj_iff (u v : Fin 12) :
    icosahedron_graph.Adj u v ↔ icosahedron_is_amply_regular_adj u v = true := by
  simp [icosahedron_is_amply_regular_adj, icosahedron_graph, SimpleGraph.fromRel,
    decide_eq_true_eq]

lemma icosahedron_is_amply_regular_nbr_mem (v w : Fin 12) :
    w ∈ icosahedron_is_amply_regular_nbr v ↔ icosahedron_graph.Adj v w := by
  simp [icosahedron_is_amply_regular_nbr, icosahedron_is_amply_regular_adj_iff]

lemma icosahedron_is_amply_regular_nbr_card (v : Fin 12) :
    (icosahedron_is_amply_regular_nbr v).card = 5 := by decide +revert

lemma icosahedron_is_amply_regular_card_adj (u v : Fin 12)
    (h : icosahedron_is_amply_regular_adj u v = true) :
    (icosahedron_is_amply_regular_nbr u ∩ icosahedron_is_amply_regular_nbr v).card = 2 := by
  have h' : ∀ a b : Fin 12, icosahedron_is_amply_regular_adj a b = true →
      (icosahedron_is_amply_regular_nbr a ∩ icosahedron_is_amply_regular_nbr b).card = 2 := by
    decide
  exact h' u v h

lemma icosahedron_is_amply_regular_card_dist_two (u v : Fin 12) (hne : u ≠ v)
    (hn : (icosahedron_is_amply_regular_nbr u ∩ icosahedron_is_amply_regular_nbr v).Nonempty) :
    (icosahedron_is_amply_regular_nbr u ∩ icosahedron_is_amply_regular_nbr v).card = 2 := by
  have h' : ∀ a b : Fin 12, a ≠ b →
      (icosahedron_is_amply_regular_nbr a ∩ icosahedron_is_amply_regular_nbr b).Nonempty →
      (icosahedron_is_amply_regular_nbr a ∩ icosahedron_is_amply_regular_nbr b).card = 2 := by
    decide
  exact h' u v hne hn

abbrev icosahedron_is_amply_regular_within_three (u v : Fin 12) : Prop :=
  u = v ∨ icosahedron_is_amply_regular_adj u v = true ∨
    (∃ w, icosahedron_is_amply_regular_adj u w = true ∧
      icosahedron_is_amply_regular_adj w v = true) ∨
    (∃ w x, icosahedron_is_amply_regular_adj u w = true ∧
      icosahedron_is_amply_regular_adj w x = true ∧ icosahedron_is_amply_regular_adj x v = true)

lemma icosahedron_is_amply_regular_within_three_all :
    ∀ u v : Fin 12, icosahedron_is_amply_regular_within_three u v := by decide

lemma icosahedron_is_amply_regular_edist_le_three (u v : Fin 12) :
    icosahedron_graph.edist u v ≤ (3 : ℕ∞) := by
  rcases icosahedron_is_amply_regular_within_three_all u v with h | h | ⟨w, h1, h2⟩ |
    ⟨w, x, h1, h2, h3⟩
  · subst h; simp
  · have hadj : icosahedron_graph.Adj u v := (icosahedron_is_amply_regular_adj_iff u v).2 h
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj]
    norm_num
  · have h1' : icosahedron_graph.Adj u w := (icosahedron_is_amply_regular_adj_iff u w).2 h1
    have h2' : icosahedron_graph.Adj w v := (icosahedron_is_amply_regular_adj_iff w v).2 h2
    have hp := SimpleGraph.edist_le (SimpleGraph.Walk.cons h1'
      (SimpleGraph.Walk.cons h2' SimpleGraph.Walk.nil) : icosahedron_graph.Walk u v)
    have h2le : icosahedron_graph.edist u v ≤ (2 : ℕ∞) := by simpa using hp
    exact h2le.trans (by norm_num)
  · have h1' : icosahedron_graph.Adj u w := (icosahedron_is_amply_regular_adj_iff u w).2 h1
    have h2' : icosahedron_graph.Adj w x := (icosahedron_is_amply_regular_adj_iff w x).2 h2
    have h3' : icosahedron_graph.Adj x v := (icosahedron_is_amply_regular_adj_iff x v).2 h3
    have hp := SimpleGraph.edist_le (SimpleGraph.Walk.cons h1' (SimpleGraph.Walk.cons h2'
      (SimpleGraph.Walk.cons h3' SimpleGraph.Walk.nil)) : icosahedron_graph.Walk u v)
    simpa using hp

lemma icosahedron_is_amply_regular_ediam_le_three :
    icosahedron_graph.ediam ≤ (3 : ℕ∞) := by
  rw [SimpleGraph.ediam_le_iff]
  exact icosahedron_is_amply_regular_edist_le_three

lemma icosahedron_is_amply_regular_ediam_ne_top : icosahedron_graph.ediam ≠ ⊤ := by
  have h := icosahedron_is_amply_regular_ediam_le_three
  intro htop
  rw [htop] at h
  exact absurd h (by simp)

lemma icosahedron_is_amply_regular_diam_le_three : icosahedron_graph.diam ≤ 3 := by
  simp only [SimpleGraph.diam]
  have := ENat.toNat_le_toNat (m := icosahedron_graph.ediam) (n := 3)
    icosahedron_is_amply_regular_ediam_le_three (by simp)
  simpa using this

lemma icosahedron_is_amply_regular_common_0_11 :
    icosahedron_graph.commonNeighbors 0 11 = ∅ := by
  have h0 : icosahedron_is_amply_regular_nbr 0 ∩ icosahedron_is_amply_regular_nbr 11 = ∅ := by
    decide
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [SimpleGraph.mem_commonNeighbors] at hx
  have hmem : x ∈ icosahedron_is_amply_regular_nbr 0 ∩ icosahedron_is_amply_regular_nbr 11 := by
    simp only [Finset.mem_inter, icosahedron_is_amply_regular_nbr_mem]
    exact hx
  rw [h0] at hmem
  exact Finset.notMem_empty x hmem

lemma icosahedron_is_amply_regular_two_lt_edist_0_11 :
    (2 : ℕ∞) < icosahedron_graph.edist 0 11 := by
  rw [SimpleGraph.two_lt_edist_iff]
  refine ⟨by decide, ?_, icosahedron_is_amply_regular_common_0_11⟩
  rw [icosahedron_is_amply_regular_adj_iff]
  decide

lemma icosahedron_is_amply_regular_nbr_eq [DecidableRel icosahedron_graph.Adj] (v : Fin 12) :
    icosahedron_graph.neighborFinset v = icosahedron_is_amply_regular_nbr v := by
  ext w
  simp [SimpleGraph.mem_neighborFinset, icosahedron_is_amply_regular_nbr_mem]

lemma icosahedron_is_amply_regular_card_common [DecidableRel icosahedron_graph.Adj]
    (u v : Fin 12) :
    Fintype.card ↑(icosahedron_graph.commonNeighbors u v) =
      (icosahedron_is_amply_regular_nbr u ∩ icosahedron_is_amply_regular_nbr v).card := by
  rw [Fintype.card_subtype (fun x => x ∈ icosahedron_graph.commonNeighbors u v)]
  congr 1
  ext x
  simp [Finset.mem_inter, icosahedron_is_amply_regular_nbr_mem, SimpleGraph.mem_commonNeighbors]

lemma icosahedron_is_amply_regular_diam_ge_three : 3 ≤ icosahedron_graph.diam := by
  have h3 : (3 : ℕ∞) ≤ icosahedron_graph.ediam :=
    (Order.add_one_le_of_lt icosahedron_is_amply_regular_two_lt_edist_0_11).trans
      SimpleGraph.edist_le_ediam
  simp only [SimpleGraph.diam]
  have := ENat.toNat_le_toNat h3 icosahedron_is_amply_regular_ediam_ne_top
  simpa using this

/-- The icosahedron graph is amply regular with parameters (5, 2, 2) and has diameter 3. -/
theorem icosahedron_is_amply_regular [DecidableRel icosahedron_graph.Adj] :
    IsAmplyRegular icosahedron_graph 5 2 2 ∧
    icosahedron_graph.diam = 3 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro v
    show (icosahedron_graph.neighborFinset v).card = 5
    rw [icosahedron_is_amply_regular_nbr_eq, icosahedron_is_amply_regular_nbr_card]
  · intro u v huv
    rw [icosahedron_is_amply_regular_card_common,
      icosahedron_is_amply_regular_card_adj u v ((icosahedron_is_amply_regular_adj_iff u v).1 huv)]
  · intro u v h
    have hne0 : icosahedron_graph.dist u v ≠ 0 := by omega
    obtain ⟨huv, hreach⟩ := SimpleGraph.dist_ne_zero_iff_ne_and_reachable.1 hne0
    have hed : icosahedron_graph.edist u v = (2 : ℕ∞) := by
      rw [← hreach.coe_dist_eq_edist, h]
      norm_num
    obtain ⟨hne, -, hnonempty⟩ := SimpleGraph.edist_eq_two_iff.1 hed
    rw [icosahedron_is_amply_regular_card_common]
    refine icosahedron_is_amply_regular_card_dist_two u v hne ?_
    obtain ⟨x, hx⟩ := hnonempty
    rw [SimpleGraph.mem_commonNeighbors] at hx
    exact ⟨x, by simp only [Finset.mem_inter, icosahedron_is_amply_regular_nbr_mem]; exact hx⟩
  · exact le_antisymm icosahedron_is_amply_regular_diam_le_three
      icosahedron_is_amply_regular_diam_ge_three
