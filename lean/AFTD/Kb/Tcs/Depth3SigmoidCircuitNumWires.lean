import AFTD.Prelude
import AFTD.Kb.Tcs.Depth3SigmoidCircuit

/-!
# depth3_sigmoid_circuit_num_wires

Topic: circuits   Node: 58da5db92377

Provenance: formalization of a published result. Source: scout/2611-21910-new-gate-weight-and-wire-complexity-bounds-for-sigmoid-neur.md:375

The total number of wires in a depth-3 sigmoidal circuit C, defined as the sum of the number of nonzero weights in w₁, w₂, and w₃.
-/

/-- Total number of wires (nonzero weights) in a depth-3 sigmoidal circuit. -/
noncomputable def depth3_sigmoid_circuit_num_wires {n : ℕ} (C : Depth3SigmoidCircuit n) : ℕ :=
  open Classical in
  (∑ j : Fin C.m₁, (Finset.univ.filter (fun i : Fin n => C.w₁ j i ≠ 0)).card) +
  (∑ k : Fin C.m₂, (Finset.univ.filter (fun j : Fin C.m₁ => C.w₂ k j ≠ 0)).card) +
  (Finset.univ.filter (fun k : Fin C.m₂ => C.w₃ k ≠ 0)).card
