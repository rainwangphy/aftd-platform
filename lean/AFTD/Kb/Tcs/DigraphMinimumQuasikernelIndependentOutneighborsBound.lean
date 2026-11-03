import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphQuasikernelOutneighbors
import AFTD.Kb.Tcs.DigraphQuasikernelOutneighborsTwoDominate

/-!
# digraph_minimum_quasikernel_independent_outneighbors_bound

Topic: graphs   Node: a82560776fb9

Provenance: helper lemma. Auxiliary lemma for the OP-337 campaign; standard finite digraph definitions and quasi-kernel exchange.

If a minimum quasi-kernel in a finite loopless source-free digraph has an independent first out-neighborhood, that neighborhood has at least as many vertices as the quasi-kernel.
-/

theorem digraph_minimum_quasikernel_independent_outneighbors_bound
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (Q : Finset α)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hsource : ∀ v, ∃ u, D.Adj u v)
    (hind : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v)
    (hcover : ∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v)
    (hmin : ∀ P : Finset α,
      (∀ u ∈ P, ∀ v ∈ P, u ≠ v → ¬ D.Adj u v) →
      (∀ v, ∃ u ∈ P, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) →
      Q.card ≤ P.card)
    (hNind : ∀ u ∈ digraph_quasikernel_outneighbors D Q,
      ∀ v ∈ digraph_quasikernel_outneighbors D Q, u ≠ v → ¬ D.Adj u v) :
    Q.card ≤ (digraph_quasikernel_outneighbors D Q).card := by
  exact hmin _ hNind (digraph_quasikernel_outneighbors_two_dominate D Q hloop hsource hind hcover)
