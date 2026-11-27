import AFTD.Prelude

/-!
# op1957_two_exceptional_slots_force_independent_triple

Topic: graphs   Node: 25f85db92125

Provenance: helper lemma. OP-1957: small-shore singleton identification

If two disjoint anticomplete barrier slots each contain a C vertex, then saturation identifies them with the two exceptional vertices, which together with the second root are pairwise nonadjacent.
-/

theorem op1957_two_exceptional_slots_force_independent_triple
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (C X Y U P Q : Finset V) (x y p q : V)
    (hxX : x ∈ X) (hyY : y ∈ Y)
    (hPU : P ⊆ U) (hQU : Q ⊆ U) (hPQ : Disjoint P Q)
    (hpC : (P ∩ C).Nonempty) (hqC : (Q ∩ C).Nonempty)
    (hfull : ∀ z ∈ C, z ≠ p → z ≠ q → G.Adj x z)
    (hXanti : ∀ a ∈ X, ∀ u ∈ U, ¬ G.Adj a u)
    (hYanti : ∀ b ∈ Y, ∀ u ∈ U, ¬ G.Adj b u)
    (hPQanti : ∀ a ∈ P, ∀ b ∈ Q, ¬ G.Adj a b) :
    ¬ G.Adj p q ∧ ¬ G.Adj y p ∧ ¬ G.Adj y q := by
  classical
  obtain ⟨u,hu⟩ := hpC
  obtain ⟨v,hv⟩ := hqC
  have huP := (Finset.mem_inter.mp hu).1
  have huC := (Finset.mem_inter.mp hu).2
  have hvQ := (Finset.mem_inter.mp hv).1
  have hvC := (Finset.mem_inter.mp hv).2
  have hu' : u = p ∨ u = q := by
    by_contra hn
    push_neg at hn
    exact hXanti x hxX u (hPU huP) (hfull u huC hn.1 hn.2)
  have hv' : v = p ∨ v = q := by
    by_contra hn
    push_neg at hn
    exact hXanti x hxX v (hQU hvQ) (hfull v hvC hn.1 hn.2)
  have huv : u ≠ v := by
    intro he; subst v
    exact Finset.disjoint_left.mp hPQ huP hvQ
  have hupq := hPQanti u huP v hvQ
  have hyp := hYanti y hyY u (hPU huP)
  have hyq := hYanti y hyY v (hQU hvQ)
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact False.elim (huv rfl)
  · exact ⟨hupq,hyp,hyq⟩
  · exact ⟨fun h => hupq h.symm,hyq,hyp⟩
  · exact False.elim (huv rfl)
