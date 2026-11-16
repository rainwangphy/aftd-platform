import AFTD.Prelude
import AFTD.Kb.Tcs.IsBraidIso
import AFTD.Kb.Tcs.PosetEdgeBraidMap

/-!
# poset_edge_braid_iso_of_order_iso_dual

Topic: combinatorics   Node: 0a6165ef6a7d

Provenance: helper lemma. arXiv:2611.15540, after Theorem 3.3

If a partially ordered set P is order isomorphic to the dual poset Qᵒᵈ, then their associated poset braid solutions poset_edge_braid_map are isomorphic.
-/

/-- An anti-isomorphism between posets P and Q induces an isomorphism between their bipartite braid solutions. -/
theorem poset_edge_braid_iso_of_order_iso_dual {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    [DecidableEq P] [DecidableEq Q] (e : P ≃o Qᵒᵈ) :
    is_braid_iso (@poset_edge_braid_map P _ _) (@poset_edge_braid_map Q _ _) := by
  classical
  let edgeEquiv : {p : P × P // p.1 ≤ p.2} ≃ {q : Q × Q // q.1 ≤ q.2} :=
    Equiv.subtypeEquiv ((e.toEquiv.prodCongr e.toEquiv).trans (Equiv.prodComm Q Q))
      (fun a => by
        show a.1 ≤ a.2 ↔ OrderDual.ofDual (e a.2) ≤ OrderDual.ofDual (e a.1)
        exact (e.le_iff_le (x := a.1) (y := a.2)).symm)
  let pointEquiv : P × ZMod 2 ≃ Q × ZMod 2 :=
    e.toEquiv.prodCongr (Equiv.addRight (1 : ZMod 2))
  let E : ({p : P × P // p.1 ≤ p.2} ⊕ (P × ZMod 2)) ≃
      ({q : Q × Q // q.1 ≤ q.2} ⊕ (Q × ZMod 2)) :=
    Equiv.sumCongr edgeEquiv pointEquiv
  have hedge : ∀ l : {p : P × P // p.1 ≤ p.2},
      (edgeEquiv l : Q × Q) = (OrderDual.ofDual (e l.1.2), OrderDual.ofDual (e l.1.1)) := by
    intro l; rfl
  have hpoint : ∀ w : P × ZMod 2,
      pointEquiv w = (OrderDual.ofDual (e w.1), w.2 + 1) := by
    intro w; rfl
  have hz1 : ∀ b : ZMod 2, b + 1 = 0 ↔ b = 1 := by
    intro b; constructor
    · intro h
      have h1 : (b + 1) = (1 + 1 : ZMod 2) := by rw [h]; decide
      exact add_right_cancel h1
    · intro h; rw [h]; decide
  have hz0 : ∀ b : ZMod 2, b + 1 = 1 ↔ b = 0 := by
    intro b; constructor
    · intro h; exact add_right_cancel h
    · intro h; rw [h]; decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hcomm : ∀ (l : {p : P × P // p.1 ≤ p.2}) (w : P × ZMod 2),
      (OrderDual.ofDual (e (if w = ((l : P × P).1, 0) then ((l : P × P).2, 1)
          else if w = ((l : P × P).2, 1) then ((l : P × P).1, 0) else w).1),
        (if w = ((l : P × P).1, 0) then ((l : P × P).2, 1)
          else if w = ((l : P × P).2, 1) then ((l : P × P).1, 0) else w).2 + 1) =
      (if (OrderDual.ofDual (e w.1), w.2 + 1) = (OrderDual.ofDual (e (l : P × P).2), 0) then
         (OrderDual.ofDual (e (l : P × P).1), 1)
       else if (OrderDual.ofDual (e w.1), w.2 + 1) = (OrderDual.ofDual (e (l : P × P).1), 1) then
         (OrderDual.ofDual (e (l : P × P).2), 0)
       else (OrderDual.ofDual (e w.1), w.2 + 1)) := by
    intro l w
    by_cases h1 : w = ((l : P × P).1, 0)
    · subst h1
      simp [h10, h11]
    · by_cases h2 : w = ((l : P × P).2, 1)
      · subst h2
        simp [h1, h11]
      · have hc1 : ¬ ((OrderDual.ofDual (e w.1), w.2 + 1) = (OrderDual.ofDual (e (l : P × P).2), 0)) := by
          intro h
          have h1' : OrderDual.ofDual (e w.1) = OrderDual.ofDual (e (l : P × P).2) := congrArg Prod.fst h
          have h2' : w.2 + 1 = 0 := congrArg Prod.snd h
          have hwe : w.1 = (l : P × P).2 := e.injective (by simpa using h1')
          have hw2 : w.2 = 1 := (hz1 w.2).mp h2'
          exact h2 (by rw [Prod.ext_iff]; exact ⟨hwe, hw2⟩)
        have hc0 : ¬ ((OrderDual.ofDual (e w.1), w.2 + 1) = (OrderDual.ofDual (e (l : P × P).1), 1)) := by
          intro h
          have h1' : OrderDual.ofDual (e w.1) = OrderDual.ofDual (e (l : P × P).1) := congrArg Prod.fst h
          have h2' : w.2 + 1 = 1 := congrArg Prod.snd h
          have hwe : w.1 = (l : P × P).1 := e.injective (by simpa using h1')
          have hw2 : w.2 = 0 := (hz0 w.2).mp h2'
          exact h1 (by rw [Prod.ext_iff]; exact ⟨hwe, hw2⟩)
        simp [h1, h2, hc1, hc0]
  refine ⟨E, ?_⟩
  funext p
  obtain ⟨a, b⟩ := p
  rcases a with l | z <;> rcases b with l' | w
  · simp [Function.comp, Prod.map, poset_edge_braid_map, E]
  · simp only [Function.comp_apply, Prod.map, poset_edge_braid_map, E, Equiv.sumCongr_apply,
      Sum.map_inl, Sum.map_inr]
    simp only [hpoint, hedge]
    exact Prod.ext (congrArg Sum.inr (hcomm l w)) rfl
  · simp only [Function.comp_apply, Prod.map, poset_edge_braid_map, E, Equiv.sumCongr_apply,
      Sum.map_inl, Sum.map_inr]
    simp only [hpoint, hedge]
    exact Prod.ext rfl (congrArg Sum.inr (hcomm l' z))
  · simp [Function.comp, Prod.map, poset_edge_braid_map, E]
