import AFTD.Prelude

/-!
# digraph_good_center_from_arc_map_budget

Topic: graphs   Node: 05cf6fde7584

Provenance: helper lemma. Final finite pigeonhole step for the small-overlap good-center route to OP-110.

For a finite digraph with a chosen common predecessor for every arc, if the number of dirty parents plus the number of missing predecessor arc-map images is smaller than the order, there is a vertex with a clean out-neighborhood whose outgoing arcs all have a common successor.
-/

theorem digraph_good_center_from_arc_map_budget
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (choose : α → α → α)
    (hchoice : ∀ u v, D.Adj u v → D.Adj (choose u v) u ∧ D.Adj (choose u v) v)
    (hbudget :
      let Arc := {e : α × α // D.Adj e.1 e.2}
      let f : Arc → Arc := fun e =>
        ⟨(choose e.val.1 e.val.2, e.val.1), (hchoice e.val.1 e.val.2 e.property).1⟩
      let dirty : Finset α := Finset.univ.filter fun u =>
        ∃ a b p, a ≠ b ∧ p ≠ u ∧ D.Adj u a ∧ D.Adj u b ∧ D.Adj p a ∧ D.Adj p b
      dirty.card + ((Finset.univ : Finset Arc) \ Finset.univ.image f).card < Fintype.card α) :
    ∃ v, (∀ a b, a ≠ b → D.Adj v a → D.Adj v b →
        ∀ p, D.Adj p a → D.Adj p b → p = v) ∧
      (∀ w, D.Adj v w → ∃ x, D.Adj v x ∧ D.Adj w x) := by
  classical
  let Arc := {e : α × α // D.Adj e.1 e.2}
  let f : Arc → Arc := fun e =>
    ⟨(choose e.val.1 e.val.2, e.val.1), (hchoice e.val.1 e.val.2 e.property).1⟩
  let dirty : Finset α := Finset.univ.filter fun u =>
    ∃ a b p, a ≠ b ∧ p ≠ u ∧ D.Adj u a ∧ D.Adj u b ∧ D.Adj p a ∧ D.Adj p b
  let missing : Finset Arc := Finset.univ \ Finset.univ.image f
  let tails : Finset α := missing.image fun e => e.val.1
  have htail : tails.card ≤ missing.card := Finset.card_image_le
  have hunion : (dirty ∪ tails).card ≤ dirty.card + tails.card := Finset.card_union_le _ _
  have hb : dirty.card + missing.card < Fintype.card α := hbudget
  have hex : ∃ v, v ∉ dirty ∧ v ∉ tails := by
    by_contra h
    have hs : (Finset.univ : Finset α) ⊆ dirty ∪ tails := by
      intro v _
      by_contra hv
      apply h
      refine ⟨v, ?_, ?_⟩
      · intro hd
        exact hv (Finset.mem_union_left _ hd)
      · intro ht
        exact hv (Finset.mem_union_right _ ht)
    have hc := Finset.card_le_card hs
    simp only [Finset.card_univ] at hc
    omega
  obtain ⟨v, hvdirty, hvtail⟩ := hex
  refine ⟨v, ?_, ?_⟩
  · intro a b hab hva hvb p hpa hpb
    by_contra hp
    apply hvdirty
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, b, p, hab, hp, hva, hvb, hpa, hpb⟩
  · intro w hvw
    let e : Arc := ⟨(v,w), hvw⟩
    have hnot : e ∉ missing := by
      intro hm
      apply hvtail
      exact Finset.mem_image.mpr ⟨e, hm, rfl⟩
    have he : e ∈ Finset.univ.image f := by
      by_contra h
      apply hnot
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩
    obtain ⟨e', _, heq⟩ := Finset.mem_image.mp he
    have hp : choose e'.val.1 e'.val.2 = v := congrArg (fun z : Arc => z.val.1) heq
    have ht : e'.val.1 = w := congrArg (fun z : Arc => z.val.2) heq
    refine ⟨e'.val.2, ?_, ?_⟩
    · simpa [hp] using (hchoice e'.val.1 e'.val.2 e'.property).2
    · simpa [ht] using e'.property
