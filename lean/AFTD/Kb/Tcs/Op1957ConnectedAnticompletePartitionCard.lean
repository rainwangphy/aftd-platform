import AFTD.Prelude

/-!
# op1957_connected_anticomplete_partition_card

Topic: graphs   Node: 7027f0901d07

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Connected anticomplete partition card.
-/

set_option maxHeartbeats 2000000

theorem op1957_connected_anticomplete_partition_card
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) (hconn : G.Connected) (J : Finset I) (F : I → Finset V)
    (hnonempty : ∀ i ∈ J, (F i).Nonempty)
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j))
    (hanti : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∀ u ∈ F i, ∀ v ∈ F j, ¬ G.Adj u v)
    (hcover : J.biUnion F = Finset.univ) : J.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hne
  obtain ⟨u,hu⟩ := hnonempty i hi
  obtain ⟨v,hv⟩ := hnonempty j hj
  have hclosed : ∀ a ∈ F i, ∀ b, G.Adj a b → b ∈ F i := by
    intro a ha b hab
    have hb : b ∈ J.biUnion F := by rw [hcover]; simp
    obtain ⟨l,hl,hbl⟩ := Finset.mem_biUnion.mp hb
    by_cases he : i=l
    · subst l
      exact hbl
    · exact False.elim (hanti i hi l hl he a ha b hbl hab)
  have hwalk : ∀ (a b : V), G.Reachable a b → a ∈ F i → b ∈ F i := by
    intro a b hab
    obtain ⟨p⟩ := hab
    induction p with
    | nil => intro ha; exact ha
    | cons hadj p ih => intro ha; exact ih (hclosed _ ha _ hadj)
  have hv' := hwalk u v (hconn u v) hu
  exact Finset.disjoint_left.mp (hdis i hi j hj hne) hv' hv
