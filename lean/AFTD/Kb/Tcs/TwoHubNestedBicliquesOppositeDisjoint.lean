import AFTD.Prelude

/-!
# two_hub_nested_bicliques_opposite_disjoint

Topic: graphs   Node: e1ca09eb3f40

Provenance: helper lemma. OP-1957 crossing-shore structural reduction, session IN-1122.

With two hub neighbors and the displayed pair of complete bipartite subgraphs, the first opposite shore is disjoint from the second shore whenever their disjoint neighbor sets exceed the degree bound.
-/

theorem two_hub_nested_bicliques_opposite_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (d : ℕ) (x y : V) (hxy : x ≠ y) (S A B W Q : Finset V)
    (hA : A ⊆ S) (hW : W ⊆ S) (hAB : Disjoint A B) (hQB : Q ⊆ B)
    (hxS : x ∉ S) (hyS : y ∉ S) (hxQ : x ∉ Q) (hyQ : y ∉ Q)
    (hsize : d < A.card + Q.card + 2)
    (hmax : ∀ v, (H.neighborFinset v).card ≤ d)
    (hSxy : ∀ v ∈ S, H.Adj v x ∧ H.Adj v y)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, H.Adj b a)
    (hQW : ∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) : Disjoint B W := by
  classical
  apply Finset.disjoint_left.mpr
  intro b hbB hbW
  have hbS : b ∈ S := hW hbW
  have hbx : H.Adj b x := (hSxy b hbS).1
  have hby : H.Adj b y := (hSxy b hbS).2
  have hAQ : Disjoint A Q := Finset.disjoint_left.mpr (by
    intro a haA haQ
    exact (Finset.disjoint_left.mp hAB) haA (hQB haQ))
  have hxA : x ∉ A := fun h => hxS (hA h)
  have hyA : y ∉ A := fun h => hyS (hA h)
  have hxU : x ∉ A ∪ Q := by simp [hxQ, hxA]
  have hyU : y ∉ A ∪ Q := by simp [hyQ, hyA]
  have hsub : insert x (insert y (A ∪ Q)) ⊆ H.neighborFinset b := by
    intro v hv
    rw [H.mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_union] at hv
    rcases hv with rfl | rfl | hv | hv
    · exact hbx
    · exact hby
    · exact hBA b hbB v hv
    · exact (hQW v hv b hbW).symm
  have hn := (Finset.card_le_card hsub).trans (hmax b)
  rw [Finset.card_insert_of_notMem (by simp [hxy, hxU]), Finset.card_insert_of_notMem hyU,
    Finset.card_union_of_disjoint hAQ] at hn
  omega
