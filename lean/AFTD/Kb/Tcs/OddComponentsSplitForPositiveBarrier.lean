import AFTD.Prelude

/-!
# odd_components_split_for_positive_barrier

Topic: graphs   Node: de30c5cb8471

Provenance: helper lemma. OP-1957: split the extra barrier vertices into one odd component and the remaining components.

Let a finite graph have at least s odd connected components, where s is positive. Either s is one and the vertex count is odd, or the vertices split into two nonempty anticomplete sets with the second set containing at least s−1 vertices.
-/

theorem odd_components_split_for_positive_barrier
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (s : ℕ) (hs : 1 ≤ s) (hodd : s ≤ H.oddComponents.ncard) :
    (s=1 ∧ Odd (Fintype.card V)) ∨
      ∃ Z W : Finset V, Z.Nonempty ∧ W.Nonempty ∧ Disjoint Z W ∧
        Z ∪ W = Finset.univ ∧ s ≤ W.card+1 ∧
        (∀ z ∈ Z, ∀ w ∈ W, ¬ H.Adj z w) := by
  classical
  by_cases hfirst : s=1 ∧ Odd (Fintype.card V)
  · exact Or.inl hfirst
  · right
    have hcount : 2 ≤ H.oddComponents.ncard := by
      by_contra h
      have heq : H.oddComponents.ncard=1 := by omega
      have ho : Odd H.oddComponents.ncard := by rw [heq]; decide
      have hv : Odd (Fintype.card V) := by
        have := (H.odd_ncard_oddComponents.mp ho)
        simpa [Nat.card_eq_fintype_card] using this
      exact hfirst ⟨by omega, hv⟩
    have hpos : 0 < H.oddComponents.ncard := by omega
    obtain ⟨c,hc⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
    let A : Set H.ConnectedComponent := H.oddComponents \ {c}
    have hA : A.ncard+1 = H.oddComponents.ncard := by
      exact Set.ncard_sdiff_singleton_add_one hc
    let Z : Finset V := c.supp.toFinset
    let W : Finset V := Finset.univ \ Z
    have hZ : Z.Nonempty := by simpa [Z] using c.nonempty_supp
    let f (d : A) : V := Classical.choose d.val.nonempty_supp
    have hf (d : A) : f d ∈ d.val.supp := Classical.choose_spec d.val.nonempty_supp
    have hfW (d : A) : f d ∈ W := by
      simp only [W, Finset.mem_sdiff, Finset.mem_univ, true_and, Z, Set.mem_toFinset]
      intro hv
      have h1 : H.connectedComponentMk (f d) = c := by
        simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hv
      have h2 : H.connectedComponentMk (f d) = d.val := by
        simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hf d
      have hdc : d.val ≠ c := by
        have := d.property.2
        simpa using this
      exact hdc (h2.symm.trans h1)
    let fW : A → {v : V // v ∈ W} := fun d => ⟨f d,hfW d⟩
    have hinj : Function.Injective fW := by
      intro d e hde
      have hval : f d = f e := congrArg Subtype.val hde
      have hd : H.connectedComponentMk (f d) = d.val := by
        simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hf d
      have he : H.connectedComponentMk (f e) = e.val := by
        simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hf e
      apply Subtype.ext
      exact hd.symm.trans ((congrArg H.connectedComponentMk hval).trans he)
    have hle : A.ncard ≤ W.card := by
      have h := Nat.card_le_card_of_injective fW hinj
      simpa [Nat.card_coe_set_eq] using h
    have hW : W.Nonempty := by
      apply Finset.card_pos.mp
      omega
    refine ⟨Z,W,hZ,hW,?_,?_,?_,?_⟩
    · apply Finset.disjoint_left.mpr
      intro v hv hw
      exact (Finset.mem_sdiff.mp hw).2 hv
    · simp [W]
    · omega
    · intro z hz w hw hzw
      have hzc : z ∈ c.supp := by simpa [Z] using hz
      have hwc : w ∉ c.supp := by simpa [W,Z] using hw
      exact hwc ((c.mem_supp_congr_adj hzw).mp hzc)
