import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_tight_two_interval_half_width_counterexample

Topic: combinatorics   Node: df08081eb48f

Provenance: helper lemma. Route audit for OP-205 / RT-1 following arXiv:2610.15635. Experiment 6491 refutes a proposed SINGLE-CLASS normalization, not a graph covering theorem or the full local-model normalization. No research advance is claimed.

A single tight rooted class with two end intervals can have a nonfull interval wider than half the radius. At radius eight the class is {0,1,3,4,5,6,7}, with a suffix of width five and a missing position two.
-/

open Finset

theorem cycle_power_dyadic_tight_two_interval_half_width_counterexample :
    ∃ b : ℕ → Bool,
      b 0 = true ∧ b 7 = true ∧ b 2 = false ∧ b 3 = true ∧
      cycle_power_dyadic_class_weight 3 b = 7 ∧
      (range 8).sum (fun a => (b a).toNat) = 7 ∧
      (∀ (a c d : Fin 8), a < c → c < d →
        b a = false → b c = true → b d = true) := by
  refine ⟨fun a => decide (a < 2 ∨ (3 ≤ a ∧ a < 8)), ?_⟩
  decide
