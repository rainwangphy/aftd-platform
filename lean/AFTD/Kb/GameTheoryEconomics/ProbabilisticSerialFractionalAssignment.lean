import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhase

/-!
# probabilistic_serial_fractional_assignment

Topic: social_choice   Node: b2dc71a2cd0e

Provenance: formalization of a published result. Source: arXiv:2611.05777 (Sublinear Metric Distortion for Matching), Sec. 1 and Sec. 6: one-sided matching of n agents to n items with ordinal rankings by distance; the probabilistic serial rule (the rule as described there: agents simultaneously eat their favourite available item at the same constant rate); written as an explicit n-phase simulation

The probabilistic serial rule for n agents and n unit-capacity items with strict rankings pref: starting from capacities 1 and nothing eaten, run n phases of the simultaneous-eating procedure (each agent eats at unit speed its favourite item with positive remaining capacity; a phase ends when the first eaten item runs out). The result X_ij is the fraction of item j consumed by agent i. Each phase exhausts an item, so n phases consume all items.
-/

/-- The probabilistic serial fractional assignment: `X i j` is the amount of unit-capacity item `j` eaten by agent `i` when all agents eat at unit speed their favourite remaining item. Run as `n` phases of `probabilistic_serial_phase`, starting with all capacities 1; each phase exhausts at least one item, so after `n` phases every item is consumed. -/
noncomputable def probabilistic_serial_fractional_assignment (n : ℕ)
    (pref : Fin n → Equiv.Perm (Fin n)) : Fin n → Fin n → ℝ :=
  ((probabilistic_serial_phase n pref)^[n] (fun _ => 1, fun _ _ => 0)).2
