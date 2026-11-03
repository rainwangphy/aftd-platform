import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphQuasikernelVertexExchange

/-!
# digraph_minimum_quasikernel_exchange_obstruction

Topic: graphs   Node: 426aecc72e5b

Provenance: helper lemma. Auxiliary lemma for the OP-337 campaign; standard finite digraph definitions and quasi-kernel exchange.

If a vertex can independently replace at least two members of a minimum quasi-kernel, then an out-neighbor of the removed members is not reached in one step from the proposed replacement set.
-/

theorem digraph_minimum_quasikernel_exchange_obstruction
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (Q C : Finset α) (x : α)
    (hCQ : C ⊆ Q) (hxQ : x ∉ Q)
    (hx_in : ∀ q ∈ Q, ¬ D.Adj q x)
    (hx_out : ∀ q ∈ Q \ C, ¬ D.Adj x q)
    (hxC : ∀ q ∈ C, D.Adj x q)
    (hind : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v)
    (hcover : ∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v)
    (hmin : ∀ P : Finset α,
      (∀ u ∈ P, ∀ v ∈ P, u ≠ v → ¬ D.Adj u v) →
      (∀ v, ∃ u ∈ P, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) →
      Q.card ≤ P.card)
    (hsize : 2 ≤ C.card) :
    ∃ q ∈ C, ∃ v, D.Adj q v ∧ ∀ r ∈ insert x (Q \ C), ¬ D.Adj r v := by
  classical
  by_contra hnone
  push Not at hnone
  have hkeep : ∀ q ∈ C, ∀ v, D.Adj q v → ∃ r ∈ insert x (Q \ C), D.Adj r v := by
    intro q hq v hqv
    exact hnone q hq v hqv
  have h := digraph_quasikernel_vertex_exchange D Q C x hCQ hxQ hx_in hx_out hxC hkeep hind hcover
  dsimp only at h
  obtain ⟨hi,hc,hcard⟩ := h
  have hbound := hmin (insert x (Q \ C)) hi hc
  omega
