import AFTD.Prelude
import AFTD.Kb.Tcs.WeakDegExecution
import AFTD.Kb.Tcs.WeakDegOp

/-!
# is_availably_weakly_d_degenerate

Topic: graphs   Node: bb9ed3fb9af6

Provenance: formalization of a published result. Source: arXiv:2611.25850: Section 1

A finite simple graph G on vertex type V with decidable equality is α-availably weakly d-degenerate for d : ℕ and α : ℝ if there exists a sequence of operations ops : List (WeakDegOp V) and a list of integer availabilities avails : List ℤ witnessing WeakDegExecution G Finset.univ (fun _ => (d : ℤ)) ops avails such that α^(Fintype.card V) ≤ (avails.prod : ℝ).
-/

/-- A finite graph is α-availably weakly d-degenerate. -/
def is_availably_weakly_d_degenerate {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) (α : ℝ) : Prop := ∃ (ops : List (WeakDegOp V)) (avails : List ℤ),
    WeakDegExecution G Finset.univ (fun _ => (d : ℤ)) ops avails ∧
      α ^ (Fintype.card V) ≤ (avails.prod : ℝ)
