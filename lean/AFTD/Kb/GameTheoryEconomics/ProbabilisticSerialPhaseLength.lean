import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhaseState

/-!
# probabilistic_serial_phase_length

Topic: social_choice   Node: af12d7d54e90

Provenance: helper lemma. Helper for the item-waiting-time reduction of OP-1158 (probabilistic serial on the line, PS <= n*OPT); reduction found 2026-11-07 for IN-608, experiments 17916, 17917

The duration of phase k of the probabilistic serial procedure (k = 0, 1, ...): the total remaining item capacity before the phase minus the total after it, divided by n. While some item is left every one of the n agents eats at unit speed, so this is the length of the phase; it is 0 once every item is used up.
-/

noncomputable def probabilistic_serial_phase_length (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (k : ℕ) : ℝ :=
  ((∑ j, (probabilistic_serial_phase_state n pref k).1 j) -
      ∑ j, (probabilistic_serial_phase_state n pref (k + 1)).1 j) / n
