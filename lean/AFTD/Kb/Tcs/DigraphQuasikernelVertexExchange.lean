import AFTD.Prelude

/-!
# digraph_quasikernel_vertex_exchange

Topic: graphs   Node: 0cd14afddd5a

Provenance: helper lemma. Auxiliary lemma for the OP-337 campaign; standard finite digraph definitions and quasi-kernel exchange.

One vertex can replace a subset of a quasi-kernel when independence holds and its insertion preserves the first out-neighborhood of each removed vertex; the resulting set is a quasi-kernel with the stated cardinality.
-/

theorem digraph_quasikernel_vertex_exchange
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (Q C : Finset α) (x : α)
    (hCQ : C ⊆ Q) (hxQ : x ∉ Q)
    (hx_in : ∀ q ∈ Q, ¬ D.Adj q x)
    (hx_out : ∀ q ∈ Q \ C, ¬ D.Adj x q)
    (hxC : ∀ q ∈ C, D.Adj x q)
    (hkeep : ∀ q ∈ C, ∀ v, D.Adj q v → ∃ r ∈ insert x (Q \ C), D.Adj r v)
    (hind : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v)
    (hcover : ∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) :
    let P := insert x (Q \ C)
    (∀ u ∈ P, ∀ v ∈ P, u ≠ v → ¬ D.Adj u v) ∧
    (∀ v, ∃ u ∈ P, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) ∧
    P.card + C.card = Q.card + 1 := by
  classical
  dsimp only
  have hxR : x ∉ Q \ C := fun h => hxQ (Finset.mem_sdiff.mp h).1
  constructor
  · intro u hu v hv huv
    rcases Finset.mem_insert.mp hu with hu | hu
    · subst u
      rcases Finset.mem_insert.mp hv with hv | hv
      · exact (huv hv.symm).elim
      · exact hx_out v hv
    · rcases Finset.mem_insert.mp hv with hv | hv
      · subst v; exact hx_in u (Finset.mem_sdiff.mp hu).1
      · exact hind u (Finset.mem_sdiff.mp hu).1 v (Finset.mem_sdiff.mp hv).1 huv
  constructor
  · intro v
    obtain ⟨u,hu,hd⟩ := hcover v
    by_cases huC : u ∈ C
    · rcases hd with heq | ha | ⟨w,haw,hwv⟩
      · subst u
        exact ⟨x, Finset.mem_insert_self _ _, Or.inr (Or.inl (hxC v huC))⟩
      · obtain ⟨r,hr,hrv⟩ := hkeep u huC v ha
        exact ⟨r, hr, Or.inr (Or.inl hrv)⟩
      · obtain ⟨r,hr,hrw⟩ := hkeep u huC w haw
        exact ⟨r, hr, Or.inr (Or.inr ⟨w,hrw,hwv⟩)⟩
    · exact ⟨u, Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hu,huC⟩),hd⟩
  · rw [Finset.card_insert_of_notMem hxR, Finset.card_sdiff_of_subset hCQ]
    have := Finset.card_le_card hCQ
    omega

-- In a minimum quasi-kernel every possible replacement of at least two
-- members has a first-neighborhood obstruction.
