import AFTD.Prelude
import AFTD.Kb.Tcs.BoundaryFiveOddSaturatedTwoOddShoresForcePatterns
import AFTD.Kb.Tcs.C

/-!
# boundary_five_odd_saturated_empty_barrier_force_patterns

Topic: graphs   Node: 2c7ccce7210d

Provenance: helper lemma. OP-1957; saturated barrier graph-to-count reduction.

Under the displayed saturated five-by-odd block, degree, separator and B-block connectedness hypotheses, an empty-separator forced-edge residual with two odd endpoint shores yields one of the three stated defect patterns.
-/

theorem in1159_absorb_even_reservoir_of_even_total
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X Y U : Finset V) (x y : V) (k : ℕ)
    (hXY : Disjoint X Y) (hXU : Disjoint X U) (hYU : Disjoint Y U)
    (hsize : X.card+Y.card+U.card=2*k)
    (hx : x ∈ X) (hy : y ∈ Y)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hanti : ∀ a ∈ U, ∀ b ∈ X, ¬ G.Adj a b)
    (hoddX : Odd X.card) (hoddY : Odd Y.card) :
    Disjoint X (Y ∪ U) ∧ X.card+(Y ∪ U).card=2*k ∧
    x ∈ X ∧ y ∈ Y ∪ U ∧ Odd (Y ∪ U).card ∧
    (∀ a ∈ X, ∀ b ∈ Y ∪ U, G.Adj a b → a=x ∧ b=y) := by
  classical
  have hu : Even U.card := by
    obtain ⟨a,ha⟩ := hoddX
    obtain ⟨b,hb⟩ := hoddY
    rcases Nat.even_or_odd U.card with h | h
    · exact h
    · obtain ⟨c,hc⟩ := h
      omega
  have hyu : Odd (Y ∪ U).card := by
    rw [Finset.card_union_of_disjoint hYU]
    exact hoddY.add_even hu
  have hsz : X.card+(Y ∪ U).card=2*k := by
    rw [Finset.card_union_of_disjoint hYU]
    omega
  refine ⟨?_,hsz,hx,Finset.mem_union_left U hy,hyu,?_⟩
  · apply Finset.disjoint_left.mpr
    intro z hzx hz
    rcases Finset.mem_union.mp hz with hzy | hzu
    · exact Finset.disjoint_left.mp hXY hzx hzy
    · exact Finset.disjoint_left.mp hXU hzx hzu
  · intro a ha b hb hab
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hcross a ha b hb hab
    · exact False.elim (hanti b hb a ha hab.symm)

theorem boundary_five_odd_saturated_empty_barrier_force_patterns
    (k c : ℕ) (hc : 7 ≤ c) (hcodd : Odd c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hconnB : (G.induce {v | v ∈ B}).Connected)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    (x p q : Fin (4*k)) (hx : x ∈ A)
    (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hxp : ¬ G.Adj x p) (hxq : ¬ G.Adj x q)
    (hfull : ∀ y ∈ C, y ≠ p → y ≠ q → G.Adj x y)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ d ∈ D, G.Adj x d)
    (y : Fin (4*k)) (hy : y ∈ C) (hyp : y ≠ p) (hyq : y ≠ q)
    (X Y U : Finset (Fin (4*k))) (hXY : Disjoint X Y)
    (hXU : Disjoint X U) (hYU : Disjoint Y U)
    (hsize : X.card + Y.card + U.card = 2*k) (hxX : x ∈ X) (hyY : y ∈ Y)
    (hoddX : Odd X.card) (hoddY : Odd Y.card)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hanti : ∀ a ∈ U, ∀ b ∈ X, ¬ G.Adj a b) :
    (∃ r ∈ ({p,q} : Finset (Fin (4*k))), ∃ U ⊆ A.erase x, U.card=2 ∧
      ∀ a ∈ U, ¬ G.Adj a y ∧ ¬ G.Adj a r) ∨
    (∀ a ∈ A.erase x, ¬ G.Adj a y) ∨
    (G.Adj p q ∧ (G.Adj y p ∨ G.Adj y q) ∧
      ∃ U ⊆ B, ∃ Z ⊆ (C \ {p,q,y}), U.card+Z.card=c-4 ∧
        (∀ b ∈ U, ¬ G.Adj b p ∧ ¬ G.Adj b q ∧ ¬ G.Adj b y) ∧
        (∀ z ∈ Z, ¬ G.Adj z p ∧ ¬ G.Adj z q ∧ ¬ G.Adj z y)) := by
  classical
  obtain ⟨hXW,hWsize,_,hyW,hWodd,hXWcross⟩ :=
    in1159_absorb_even_reservoir_of_even_total G X Y U x y k hXY hXU hYU hsize
      hxX hyY hcross hanti hoddX hoddY
  exact boundary_five_odd_saturated_two_odd_shores_force_patterns k c hc hcodd hkc G A B C D
    hAB hAC hAD hBC hBD hCD hcover hA hB hC hD hnoAB hnoCD hconnB hdegree hsep
    x p q hx hp hq hpq hxp hxq hfull hsatA hsatD y hy hyp hyq
    X (Y ∪ U) hXW hWsize hxX hyW hoddX hWodd hXWcross
