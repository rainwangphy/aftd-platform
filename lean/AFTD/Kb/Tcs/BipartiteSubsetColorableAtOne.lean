import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteSubsetStandardListColorable
import AFTD.Kb.Tcs.BipartiteSubsetGraph

/-!
# bipartite_subset_colorable_at_one

Topic: graphs   Node: 808353deba1b

Provenance: helper lemma. arXiv:2610.42094, Definition 1.2; elementary lower-bound step for OP-861.

For every k at least two, the bipartite subset graph with intersection threshold one is colorable from its standard lists.
-/

lemma bipartite_subset_colorable_at_one_exists_consec (k : ℕ) [NeZero (2 * k - 1)] (hk : 2 ≤ k)
    (S : Finset (Fin (2 * k - 1))) (hS : S.card = k) :
    ∃ x ∈ S, x + 1 ∈ S := by
  let e : Equiv.Perm (Fin (2 * k - 1)) := Equiv.addRight 1
  let S' := S.map e.toEmbedding
  have hS' : S'.card = k := by rw [Finset.card_map, hS]
  have h_union : (S ∪ S').card ≤ 2 * k - 1 := by
    calc (S ∪ S').card ≤ Fintype.card (Fin (2 * k - 1)) := Finset.card_le_univ (S ∪ S')
    _ = 2 * k - 1 := Fintype.card_fin (2 * k - 1)
  have h_inter : 1 ≤ (S ∩ S').card := by
    have h_sum := Finset.card_union_add_card_inter S S'
    omega
  have h_nonempty : (S ∩ S').Nonempty := Finset.card_pos.mp (by omega)
  rcases h_nonempty with ⟨y, hy⟩
  rw [Finset.mem_inter, Finset.mem_map] at hy
  rcases hy with ⟨hyS, ⟨x, hxS, hxeq⟩⟩
  dsimp [e] at hxeq
  rw [← hxeq] at hyS
  exact ⟨x, hxS, hyS⟩

lemma bipartite_subset_colorable_at_one_fin_add_one_ne_self (n : ℕ) [NeZero n] (hn : 2 ≤ n) (x : Fin n) :
    x + 1 ≠ x := by
  intro h
  have h1 : (1 : Fin n) = 0 := by
    have : (1 + x) - x = x - x := by rw [add_comm 1 x, h]
    rwa [add_sub_cancel_right, sub_self] at this
  have h2 : (1 : Fin n).val = (0 : Fin n).val := congrArg Fin.val h1
  rw [Fin.val_zero, Fin.val_one' n] at h2
  have : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  omega

noncomputable def bipartite_subset_colorable_at_one_choose_color (k : ℕ) [NeZero (2 * k - 1)] (hk : 2 ≤ k)
    (S : { S : Finset (Fin (2 * k - 1)) // S.card = k }) : Fin (2 * k - 1) :=
  Classical.choose (bipartite_subset_colorable_at_one_exists_consec k hk S.1 S.2)

lemma bipartite_subset_colorable_at_one_choose_color_spec (k : ℕ) [NeZero (2 * k - 1)] (hk : 2 ≤ k)
    (S : { S : Finset (Fin (2 * k - 1)) // S.card = k }) :
    bipartite_subset_colorable_at_one_choose_color k hk S ∈ S.1 ∧
      bipartite_subset_colorable_at_one_choose_color k hk S + 1 ∈ S.1 :=
  Classical.choose_spec (bipartite_subset_colorable_at_one_exists_consec k hk S.1 S.2)

theorem bipartite_subset_colorable_at_one (k : ℕ) (hk : 2 ≤ k) : bipartite_subset_standard_list_colorable k 1 := by
  have : NeZero (2 * k - 1) := ⟨by omega⟩
  have h_2le : 2 ≤ 2 * k - 1 := by omega
  let col (v : { S : Finset (Fin (2 * k - 1)) // S.card = k } ⊕ { T : Finset (Fin (2 * k - 1)) // T.card = k }) :
      Fin (2 * k - 1) :=
    Sum.elim (bipartite_subset_colorable_at_one_choose_color k hk)
             (bipartite_subset_colorable_at_one_choose_color k hk) v
  have h_cases : ∀ (S T : { S : Finset (Fin (2 * k - 1)) // S.card = k }),
      (S.1 ∩ T.1).card ≤ 1 →
        bipartite_subset_colorable_at_one_choose_color k hk S ≠
        bipartite_subset_colorable_at_one_choose_color k hk T := by
    intro S T hadj heq
    have hS := bipartite_subset_colorable_at_one_choose_color_spec k hk S
    have hT := bipartite_subset_colorable_at_one_choose_color_spec k hk T
    set x := bipartite_subset_colorable_at_one_choose_color k hk S
    have hxS : x ∈ S.1 := hS.1
    have hxS1 : x + 1 ∈ S.1 := hS.2
    have hxT : x ∈ T.1 := heq ▸ hT.1
    have hxT1 : x + 1 ∈ T.1 := heq ▸ hT.2
    let P : Finset (Fin (2 * k - 1)) := {x, x + 1}
    have hP_card : P.card = 2 := by
      rw [Finset.card_pair]
      exact (bipartite_subset_colorable_at_one_fin_add_one_ne_self (2 * k - 1) h_2le x).symm
    have hP_sub : P ⊆ S.1 ∩ T.1 := by
      intro y hy
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hxS, hxT⟩
      · exact Finset.mem_inter.mpr ⟨hxS1, hxT1⟩
    have h_le := Finset.card_le_card hP_sub
    rw [hP_card] at h_le
    omega
  have h_valid : ∀ {v w}, (bipartite_subset_graph k 1).Adj v w → col v ≠ col w := by
    intro v w hadj
    cases v with
    | inl S =>
      cases w with
      | inl S' => exact False.elim hadj
      | inr T =>
        dsimp [bipartite_subset_graph] at hadj
        dsimp [col]
        exact h_cases S T hadj
    | inr T =>
      cases w with
      | inr T' => exact False.elim hadj
      | inl S =>
        dsimp [bipartite_subset_graph] at hadj
        dsimp [col]
        exact (h_cases S T hadj).symm
  let c : (bipartite_subset_graph k 1).Coloring (Fin (2 * k - 1)) :=
    SimpleGraph.Coloring.mk col (fun {v w} => h_valid)
  use c
  intro v
  cases v with
  | inl S =>
    dsimp [c, col]
    exact (bipartite_subset_colorable_at_one_choose_color_spec k hk S).1
  | inr T =>
    dsimp [c, col]
    exact (bipartite_subset_colorable_at_one_choose_color_spec k hk T).1
