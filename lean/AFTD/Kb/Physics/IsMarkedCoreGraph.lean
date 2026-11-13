import AFTD.Prelude

/-!
# is_marked_core_graph

Topic: quantum_mechanics   Node: 717762b8e0c3

Provenance: original. Related work: arXiv:2611.08593

For natural numbers k, d, c, a simple graph J on Fin (k + 1), and a marked vertex s : Fin (k + 1), is_marked_core_graph k d c J s asserts that J is connected and triangle-free, J has d * (k + 1) + c edges, the marked vertex s has degree d, and the open-neighborhood equivalence class of s is the singleton {s} (that is, any vertex with the same neighbor set as s is equal to s).
-/

/-- Predicate asserting that a pair (J, s) of a simple graph J on Fin (k+1) and a vertex s is a marked core graph with parameters k, d, c. -/
def is_marked_core_graph (k d c : ℕ)
    (J : SimpleGraph (Fin (k + 1)))
    (s : Fin (k + 1)) : Prop :=
  J.Connected ∧
  J.CliqueFree 3 ∧
  Nat.card J.edgeSet = d * (k + 1) + c ∧
  Nat.card (J.neighborSet s) = d ∧
  (∀ v : Fin (k + 1), J.neighborSet v = J.neighborSet s → v = s)
