import AFTD.Prelude
import AFTD.Kb.Tcs.WeakDegOp
import AFTD.Kb.Tcs.WeakDegVertex
import AFTD.Kb.Tcs.WeakDegIsLegal
import AFTD.Kb.Tcs.WeakDegOpAvail
import AFTD.Kb.Tcs.WeakDegNextBound

/-!
# WeakDegExecution

Topic: graphs   Node: 976212807ccc

Provenance: formalization of a published result. Source: arXiv:2611.25850: Section 1

Inductive execution predicate WeakDegExecution G S f ops avails asserting that the sequence of operations ops : List (WeakDegOp V) together with the list of integer availabilities avails : List ℤ forms a valid elimination sequence on the finite set of remaining vertices S : Finset V with respect to the simple graph G on V (with DecidableEq V) and integer-valued bound function f : V → ℤ (with base case nil on the empty set producing empty lists [] [], and inductive step cons adding op and its availability).
-/

/-- Execution of a sequence of weak degeneracy operations recording both the operations and their availabilities. -/
inductive WeakDegExecution {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    Finset V → (V → ℤ) → List (WeakDegOp V) → List ℤ → Prop where
  | nil (f : V → ℤ) : WeakDegExecution G ∅ f [] []
  | cons (S : Finset V) (f : V → ℤ) (op : WeakDegOp V) (ops : List (WeakDegOp V))
      (avails : List ℤ)
      (hlegal : weak_deg_is_legal G S f op)
      (hexec : WeakDegExecution G (S.erase (weak_deg_vertex op))
        (weak_deg_next_bound G S f op) ops avails) :
      WeakDegExecution G S f (op :: ops) (weak_deg_op_avail f op :: avails)
