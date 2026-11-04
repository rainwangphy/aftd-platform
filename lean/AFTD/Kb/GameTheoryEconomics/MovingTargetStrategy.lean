import AFTD.Prelude

/-!
# MovingTargetStrategy

Topic: combinatorial_games   Node: c7e5bf7776fd

Provenance: formalization of a published result. Source: arXiv:2611.01281 Definition 2.1

An inductive datatype `MovingTargetStrategy` parameterized by a type `V : Type*`, with two constructors: `stop : MovingTargetStrategy V` representing termination; and `query : Finset V → MovingTargetStrategy V → MovingTargetStrategy V → MovingTargetStrategy V`, which takes a finite subset of vertices Q : Finset V and two continuation strategies for the negative (false) and positive (true) answers.
-/

/-- A finite adaptive search strategy over a vertex type V. -/
inductive MovingTargetStrategy (V : Type*) | stop : MovingTargetStrategy V
  | query : Finset V → MovingTargetStrategy V → MovingTargetStrategy V → MovingTargetStrategy V
