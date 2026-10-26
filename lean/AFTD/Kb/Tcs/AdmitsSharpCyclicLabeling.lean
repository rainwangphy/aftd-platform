import AFTD.Prelude
import AFTD.Kb.Tcs.IsSharpCyclicLabeling

/-!
# admits_sharp_cyclic_labeling

Topic: combinatorics   Node: 5c59abf7a448

Provenance: formalization of a published result. Source: arXiv:2610.31807 Definition 3.12

A simple graph G on N vertices admits a sharp cyclic labeling if there exists a bijection π from ZMod N to V(G) such that is_sharp_cyclic_labeling N G π holds.
-/

/-- A simple graph G admits a sharp cyclic labeling if there exists a bijection π : ZMod N ≃ V that is a sharp cyclic labeling. -/
def admits_sharp_cyclic_labeling {V : Type*} (N : ℕ) [NeZero N] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop := ∃ π : ZMod N ≃ V, is_sharp_cyclic_labeling N G π
