import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhase

/-!
# probabilistic_serial_phase_state

Topic: social_choice   Node: 471dcfe6499c

Provenance: helper lemma. Helper for the item-waiting-time reduction of OP-1158 (probabilistic serial on the line, PS <= n*OPT); reduction found 2026-11-07 for IN-608, experiments 17916, 17917

The state of the probabilistic serial (simultaneous eating) procedure for n agents and n unit-capacity items with rankings pref after its first k phases, started from full capacities and nothing eaten: the pair (remaining capacity of each item, amount of each item eaten so far by each agent). After n phases it is the probabilistic serial assignment.
-/

noncomputable def probabilistic_serial_phase_state (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (k : ℕ) : (Fin n → ℝ) × (Fin n → Fin n → ℝ) :=
  (probabilistic_serial_phase n pref)^[k] (fun _ => 1, fun _ _ => 0)
