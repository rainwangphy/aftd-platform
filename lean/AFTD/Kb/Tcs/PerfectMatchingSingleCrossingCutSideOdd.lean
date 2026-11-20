import AFTD.Prelude

/-!
# perfect_matching_single_crossing_cut_side_odd

Topic: graphs   Node: b09b86559a33

Provenance: helper lemma. OP-1957 first forced-edge bridge partition.

If a perfect matching crosses a vertex cut in a single edge, each side has odd size.
-/

theorem perfect_matching_single_crossing_cut_side_odd {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (A B : Finset V) (u v : V) (hdisj : Disjoint A B) (hcover : A ∪ B = Finset.univ)
    (hu : u ∈ A) (hv : v ∈ B) (huv : P.Adj u v)
    (hcut : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b → a = u ∧ b = v) : Odd A.card := by
  classical
  let T := P.induce {a | a ∈ A.erase u}
  have hT : T.IsMatching := by
    intro a ha
    have ha' : a ∈ A.erase u := ha
    have hau : a ≠ u := Finset.ne_of_mem_erase ha'
    have haA : a ∈ A := Finset.mem_of_mem_erase ha'
    obtain ⟨b,hab,huniq⟩ := hP.1 (hP.2 a)
    have hbu : b ≠ u := by
      intro h
      subst b
      have hva : v = a := hP.1.eq_of_adj_left huv hab.symm
      exact (Finset.disjoint_left.mp hdisj) (hva ▸ haA) hv
    have hbA : b ∈ A := by
      have hbU : b ∈ A ∪ B := by rw [hcover]; exact Finset.mem_univ b
      rcases Finset.mem_union.mp hbU with hbA | hbB
      · exact hbA
      · exact (hau (hcut a haA b hbB (P.adj_sub hab)).1).elim
    have hb' : b ∈ A.erase u := Finset.mem_erase.mpr ⟨hbu,hbA⟩
    refine ⟨b, ⟨ha',hb',hab⟩, ?_⟩
    intro c hc
    exact huniq c hc.2.2
  have heven : Even (A.erase u).card := by
    have h := hT.even_card
    have hcard : T.verts.toFinset = A.erase u := by ext a; simp [T]
    rw [hcard] at h
    exact h
  rw [Finset.card_erase_of_mem hu] at heven
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨u,hu⟩
  obtain ⟨m,hm⟩ := heven
  refine ⟨m, ?_⟩
  omega
