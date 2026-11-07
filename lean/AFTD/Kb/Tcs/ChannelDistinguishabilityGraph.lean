import AFTD.Prelude
import AFTD.Kb.Tcs.DiscreteMemorylessChannel

/-!
# channel_distinguishability_graph

Topic: information   Node: c536f09ba296

Provenance: formalization of a published result. Source: arXiv:2610.41977, Section 5, Equation (5.1); Shannon 1956

The distinguishability graph D(W) of a discrete memoryless channel W has inputs as vertices, with two distinct inputs adjacent if and only if their output supports are disjoint.
-/

/-- The distinguishability graph of a discrete memoryless channel has input vertices adjacent when their output supports are disjoint. -/
def channel_distinguishability_graph {A Y : Type*} [Fintype Y]
    (W : DiscreteMemorylessChannel A Y) : SimpleGraph A where
  Adj a a' := a ≠ a' ∧ Disjoint {y : Y | 0 < W.prob a y} {y : Y | 0 < W.prob a' y}
  symm := ⟨fun _ _ ⟨hne, hd⟩ => ⟨hne.symm, hd.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩
