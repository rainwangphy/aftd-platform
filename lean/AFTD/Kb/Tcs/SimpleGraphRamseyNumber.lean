import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphRamseyProperty

/-!
# simple_graph_ramsey_number

Topic: combinatorics   Node: 87fff1685c07

Provenance: formalization of a published result. Source: arXiv:2610.36522

The Ramsey number R(F, H) is the smallest positive integer N such that every graph on N vertices contains F or its complement contains H.
-/

/-- The 2-color Ramsey number R(F, H) of two simple graphs F and H. -/
noncomputable def simple_graph_ramsey_number {α β : Type*} (F : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ simple_graph_ramsey_property F H N}
