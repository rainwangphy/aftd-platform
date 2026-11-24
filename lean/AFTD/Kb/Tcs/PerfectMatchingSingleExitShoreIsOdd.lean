import AFTD.Prelude

/-!
# perfect_matching_single_exit_shore_is_odd

Topic: graphs   Node: 76ee13206c17

Provenance: helper lemma. OP-1957, forced-edge barrier endpoint parity

If a perfect matching crosses a finite vertex set only along a specified edge, then that set has odd cardinality.
-/

set_option maxHeartbeats 3000000

theorem perfect_matching_single_exit_shore_is_odd {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (P : G.Subgraph) (hP : P.IsPerfectMatching) (X : Finset V) (x y : V) (hx : x ∈ X) (hy : y ∉ X) (hxy : P.Adj x y) (hclosed : ∀ a ∈ X, ∀ b, P.Adj a b → b ∉ X → a=x ∧ b=y) : Odd X.card := by
  classical
  let F : Finset V := X.erase x
  let C : Set V := F
  have hmatch : (P.induce C).IsMatching := by
    intro a ha
    have haF : a ∈ F := ha
    have haX : a ∈ X := (Finset.mem_erase.mp haF).2
    have hax : a ≠ x := (Finset.mem_erase.mp haF).1
    obtain ⟨b,hab,huniq⟩ := hP.1 (hP.2 a)
    have hbx : b ≠ x := by
      intro he
      subst b
      have hay : a = y := (hP.1 (hP.2 x)).unique hab.symm hxy
      exact hy (hay ▸ haX)
    have hbX : b ∈ X := by
      by_contra hbX
      exact hax (hclosed a haX b hab hbX).1
    have hbF : b ∈ F := Finset.mem_erase.mpr ⟨hbx,hbX⟩
    refine ⟨b,⟨haF,hbF,hab⟩,?_⟩
    intro z hz
    exact huniq z hz.2.2
  have he := hmatch.even_card
  rw [← Set.ncard_eq_toFinset_card'] at he
  have hF : (P.induce C).verts.ncard = F.card := by
    show C.ncard = _
    simp [C]
  rw [hF] at he
  have hcard : F.card + 1 = X.card := Finset.card_erase_add_one hx
  obtain ⟨n,hn⟩ := he
  apply Nat.odd_iff.mpr
  omega
