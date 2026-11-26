import AFTD.Prelude

/-!
# saturated_barrier_other_shores_subset_block_and_three_vertices

Topic: graphs   Node: 6c69372c9ec2

Provenance: helper lemma. OP-1957; forced-edge saturated barrier reduction.

Under the displayed saturated four-block and forced-edge shore assumptions, the two shores opposite the distinguished vertex lie in B together with p, q and the opposite endpoint y.
-/

theorem saturated_barrier_other_shores_subset_block_and_three_vertices
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B C D X Y U : Finset V) (x y p q : V)
    (hAC : Disjoint A C) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hx : x ∈ X) (hy : y ∈ C)
    (hXY : Disjoint X Y) (hXU : Disjoint X U)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hanti : ∀ a ∈ U, ¬ G.Adj x a)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ d ∈ D, G.Adj x d)
    (hfull : ∀ z ∈ C, z ≠ p → z ≠ q → G.Adj x z) :
    Y ∪ U ⊆ B ∪ {p,q,y} := by
  classical
  intro z hz
  have hzx : z ≠ x := by
    intro h
    subst z
    rcases Finset.mem_union.mp hz with hz | hz
    · exact Finset.disjoint_left.mp hXY hx hz
    · exact Finset.disjoint_left.mp hXU hx hz
  have hxf : G.Adj x z → z = y := by
    intro h
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (hcross x hx z hz h).2
    · exact False.elim (hanti z hz h)
  have hzpart : z ∈ A ∪ B ∪ C ∪ D := by rw [hcover]; simp
  simp only [Finset.mem_union] at hzpart
  rcases hzpart with ((ha | hb) | hc) | hd
  · have he := hxf (hsatA z ha hzx)
    exact False.elim (Finset.disjoint_left.mp hAC ha (he ▸ hy))
  · exact Finset.mem_union_left _ hb
  · by_cases hp : z=p
    · simp [hp]
    · by_cases hq : z=q
      · simp [hq]
      · have he := hxf (hfull z hc hp hq)
        simp [he]
  · have he := hxf (hsatD z hd)
    exact False.elim (Finset.disjoint_left.mp hCD (he ▸ hy) hd)
