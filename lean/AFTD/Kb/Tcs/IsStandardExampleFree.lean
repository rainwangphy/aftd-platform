import AFTD.Prelude
import AFTD.Kb.Tcs.StandardExamplePartialOrder
import AFTD.Kb.Tcs.StandardExample

/-!
# is_standard_example_free

Topic: combinatorics   Node: 4f87076bb003

Provenance: formalization of a published result. Source: arXiv:2610.24774 Section 1

A poset P is S_k-free when it does not contain the standard example S_k of order k as an induced subposet.
-/

/-- A poset P is S_k-free if it contains no induced subposet isomorphic to the standard example of order k. -/
def is_standard_example_free (P : Type*) [PartialOrder P] (k : ℕ) : Prop := IsEmpty (StandardExample k ↪o P)
