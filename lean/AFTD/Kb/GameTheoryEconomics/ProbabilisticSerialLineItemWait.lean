import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhaseState
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhaseLength

/-!
# probabilistic_serial_line_item_wait

Topic: social_choice   Node: cffcf06abf32

Provenance: helper lemma. Helper for the item-waiting-time reduction of OP-1158 (probabilistic serial on the line, PS <= n*OPT); reduction found 2026-11-07 for IN-608, experiments 17916, 17917

The waiting cost of item j in the probabilistic serial procedure, items at real positions b: the integral, over the times t in [0,1] after item j has been used up, of the distance from b_j to the nearest item not yet used up at time t. In phases: the sum over the n phases k of (length of phase k) times (the distance from b_j to the nearest item with positive remaining capacity at the start of phase k), counting only the phases at whose start item j has no capacity left and some item still has some.
-/

noncomputable def probabilistic_serial_line_item_wait {n : ℕ} (b : Fin n → ℝ)
    (pref : Fin n → Equiv.Perm (Fin n)) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.range n,
    if h : (probabilistic_serial_phase_state n pref k).1 j ≤ 0 ∧
        (Finset.univ.filter (fun j' => 0 < (probabilistic_serial_phase_state n pref k).1 j')).Nonempty
    then probabilistic_serial_phase_length n pref k *
      (Finset.univ.filter (fun j' => 0 < (probabilistic_serial_phase_state n pref k).1 j')).inf' h.2
        (fun j' => |b j - b j'|)
    else 0
