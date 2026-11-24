import AFTD.Prelude

/-!
# saturated_barrier_other_shores_avoid_outer_blocks

Topic: graphs   Node: 206c84ffdd86

Provenance: helper lemma. OP-1957, saturation to barrier block counts

Under the displayed saturation and forced-edge shore conditions, both other barrier shores avoid the saturated vertex block and its adjacent outer block.
-/

theorem saturated_barrier_other_shores_avoid_outer_blocks
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A C D X Y U : Finset V) (x y : V)
    (hAC : Disjoint A C) (hCD : Disjoint C D)
    (hXY : Disjoint X Y) (hUX : Disjoint U X)
    (hx : x ∈ X) (hy : y ∈ Y) (hyC : y ∈ C)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hanti : ∀ u ∈ U, ∀ v ∈ X, ¬ G.Adj u v)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ d ∈ D, G.Adj x d) :
    Disjoint Y A ∧ Disjoint Y D ∧ Disjoint U A ∧ Disjoint U D := by
  classical
  have hYx : x ∉ Y := fun h => Finset.disjoint_left.mp hXY hx h
  have hUx : x ∉ U := fun h => Finset.disjoint_left.mp hUX h hx
  constructor
  · apply Finset.disjoint_left.mpr
    intro z hzY hzA
    have hzx : z ≠ x := fun h => hYx (h ▸ hzY)
    have hzy := (hcross x hx z hzY (hsatA z hzA hzx)).2
    exact Finset.disjoint_left.mp hAC hzA (hzy ▸ hyC)
  constructor
  · apply Finset.disjoint_left.mpr
    intro z hzY hzD
    have hzy := (hcross x hx z hzY (hsatD z hzD)).2
    exact Finset.disjoint_left.mp hCD (hzy ▸ hyC) hzD
  constructor
  · apply Finset.disjoint_left.mpr
    intro z hzU hzA
    have hzx : z ≠ x := fun h => hUx (h ▸ hzU)
    exact hanti z hzU x hx (hsatA z hzA hzx).symm
  · apply Finset.disjoint_left.mpr
    intro z hzU hzD
    exact hanti z hzU x hx (hsatD z hzD).symm
