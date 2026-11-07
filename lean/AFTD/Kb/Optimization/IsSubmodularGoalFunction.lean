import AFTD.Prelude
import AFTD.Kb.Optimization.PartialAssignmentLe
import AFTD.Kb.Optimization.IsMstCertificate

/-!
# is_submodular_goal_function

Topic: submodular   Node: 80d04889f437

Provenance: formalization of a published result. Source: scout/2610-40844-stochastic-minimum-spanning-tree-identification-with-binary.md:686

A function g : (G.edgeSet → Option Bool) → ℕ is a submodular goal function with goal value Q for G if: g evaluates to 0 on the empty assignment (fun _ => none); g is monotone under partial assignment extension (partial_assignment_le β γ → g β ≤ g γ); g satisfies state-dependent submodularity (for all β ≼ γ and e with γ e = none, g(γ_{e ← s}) + g(β) ≤ g(β_{e ← s}) + g(γ)); and g(β) = Q if and only if β is an MST identification certificate for G (is_mst_certificate G β).
-/

open scoped Classical in
/-- A submodular goal function with goal value Q for stochastic MST identification. -/
def is_submodular_goal_function {V : Type*} [Fintype V] (G : SimpleGraph V)
    (g : (G.edgeSet → Option Bool) → ℕ) (Q : ℕ) : Prop := g (fun _ => none) = 0 ∧
  (∀ β γ, partial_assignment_le β γ → g β ≤ g γ) ∧
  (∀ β γ e s, partial_assignment_le β γ → γ e = none →
    g (Function.update γ e (some s)) + g β ≤ g (Function.update β e (some s)) + g γ) ∧
  (∀ β, g β = Q ↔ is_mst_certificate G β)
