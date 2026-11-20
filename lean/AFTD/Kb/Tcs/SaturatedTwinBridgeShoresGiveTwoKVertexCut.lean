import AFTD.Prelude

/-!
# saturated_twin_bridge_shores_give_two_k_vertex_cut

Topic: graphs   Node: abc22f0fb631

Provenance: helper lemma. The second bridge and saturated first-witness twins yield a 2k-vertex separator in the OP-1957 general equality branch.

In a graph on 2k+2j vertices, suppose a nonempty set W and a set Q are disjoint, x and y are distinct and outside both, |W|+|Q|+2=2j, and W has no edges to Q or to x,y. Then there is a vertex separator of exactly 2k vertices with nonempty sides.
-/

theorem saturated_twin_bridge_shores_give_two_k_vertex_cut
    (k j : ℕ) (G : SimpleGraph (Fin (2 * k + 2 * j)))
    (W Q : Finset (Fin (2 * k + 2 * j))) (x y : Fin (2 * k + 2 * j))
    (hW : W.Nonempty) (hdisj : Disjoint W Q) (hxy : x ≠ y)
    (hxW : x ∉ W) (hyW : y ∉ W) (hxQ : x ∉ Q) (hyQ : y ∉ Q)
    (hsize : W.card + Q.card + 2 = 2 * j)
    (hcross : ∀ w ∈ W, ∀ q ∈ Q, ¬ G.Adj w q)
    (htwins : ∀ w ∈ W, ¬ G.Adj w x ∧ ¬ G.Adj w y) :
    ∃ C A B : Finset (Fin (2 * k + 2 * j)),
      C.card = 2 * k ∧ A.Nonempty ∧ B.Nonempty ∧
      Disjoint C A ∧ Disjoint C B ∧ Disjoint A B ∧
      C ∪ A ∪ B = Finset.univ ∧
      ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
  let A := W
  let B := insert x (insert y Q)
  let C := (A ∪ B)ᶜ
  have hAB : Disjoint A B := by
    dsimp [A, B]
    rw [Finset.disjoint_insert_right, Finset.disjoint_insert_right]
    refine ⟨hxW, hyW, hdisj⟩
  refine ⟨C, A, B, ?_, hW, Finset.insert_nonempty x _, ?_, ?_, hAB, ?_, ?_⟩
  · have hxyQ : x ∉ insert y Q := by
      simp [hxQ, hxy]
    have hBcard : B.card = Q.card + 2 := by
      dsimp [B]
      rw [Finset.card_insert_of_notMem hxyQ, Finset.card_insert_of_notMem hyQ]
    have hABcard : (A ∪ B).card = 2 * j := by
      rw [Finset.card_union_of_disjoint hAB, hBcard]
      omega
    dsimp [C]
    rw [Finset.card_compl, Fintype.card_fin, hABcard]
    omega
  · dsimp [C]
    exact disjoint_compl_left.mono_right Finset.subset_union_left
  · dsimp [C]
    exact disjoint_compl_left.mono_right Finset.subset_union_right
  · dsimp [C]
    rw [Finset.union_assoc]
    exact compl_sup_eq_top
  · intro a ha b hb
    simp only [B, Finset.mem_insert] at hb
    rcases hb with rfl | rfl | hbQ
    · exact (htwins a ha).1
    · exact (htwins a ha).2
    · exact hcross a ha b hbQ
