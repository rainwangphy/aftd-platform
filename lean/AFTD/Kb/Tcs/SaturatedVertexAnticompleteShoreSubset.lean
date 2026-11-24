import AFTD.Prelude

/-!
# saturated_vertex_anticomplete_shore_subset

Topic: graphs   Node: 43fb45cf6eed

Provenance: helper lemma. OP-1957, essential-edge barrier classification

A shore anticomplete to a saturated vertex is contained in the large opposite block together with the two distinguished nonneighbors.
-/

theorem saturated_vertex_anticomplete_shore_subset
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B C D X U : Finset V) (x p q : V)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hx : x ∈ X) (hUX : Disjoint U X)
    (hanti : ∀ u ∈ U, ∀ v ∈ X, ¬ G.Adj u v)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ d ∈ D, G.Adj x d)
    (hfull : ∀ y ∈ C, y ≠ p → y ≠ q → G.Adj x y) :
    U ⊆ B ∪ {p,q} := by
  classical
  intro u hu
  have hux : u ≠ x := by
    intro e
    subst u
    exact Finset.disjoint_left.mp hUX hu hx
  have hna : ¬ G.Adj u x := hanti u hu x hx
  have hucover : u ∈ A ∪ B ∪ C ∪ D := by rw [hcover]; simp
  simp only [Finset.mem_union] at hucover
  rcases hucover with ((ha | hb) | hc) | hd
  · exact False.elim (hna (hsatA u ha hux).symm)
  · exact Finset.mem_union_left _ hb
  · by_cases hp : u = p
    · simp [hp]
    · by_cases hq : u = q
      · simp [hq]
      · exact False.elim (hna (hfull u hc hp hq).symm)
  · exact False.elim (hna (hsatD u hd).symm)
