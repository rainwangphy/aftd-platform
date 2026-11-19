import AFTD.Prelude

/-!
# complete_coloring_classical_value

Topic: quantum   Node: a5a387c788c1

Provenance: formalization of a published result. Source: arXiv:2611.19002, Quantum Coloring Games on Complete Graphs, Section 3.1

The expected payoff of a pure classical strategy pair (a, b) in the complete-graph coloring game with n inputs and m colors at input-equality probability p.
-/

/-- The expected payoff of classical strategy pair (a, b) at equality probability p in the complete-graph coloring game. -/
noncomputable def complete_coloring_classical_value (n m : ℕ) (p : ℝ) (a b : Fin n → Fin m) : ℝ :=
  p * (((Finset.univ : Finset (Fin n)).filter (fun x => a x = b x)).card / (n : ℝ)) +
  (1 - p) * (((Finset.univ : Finset (Fin n × Fin n)).filter (fun xy => xy.1 ≠ xy.2 ∧ a xy.1 ≠ b xy.2)).card / ((n : ℝ) * (n - 1)))
