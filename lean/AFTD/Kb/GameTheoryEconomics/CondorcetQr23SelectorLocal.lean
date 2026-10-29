import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorMember
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorChallenger
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorNext
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorPotential

/-!
# condorcet_qr23_selector_local

Topic: social_choice   Node: fc4e2898901e

Provenance: helper lemma. Certificate data for condorcet_tournament_stationary_restriction_obstruction (restriction diagnostic for OP-19 on the quadratic-residue tournament modulo 23; potential from experiment 8584, recomputed by CP-SAT). Related definition from Condorcet winning sets, Social Choice and Welfare 44(3):493-517 (2015).

The potential satisfies 23 + 3 p(i) <= 45 [challenger below the minimum] + the sum of p over the three transitions, for every triple.
-/

theorem condorcet_qr23_selector_local : ∀ i : Fin 1771, 23 + 3 * condorcet_qr23_selector_potential i ≤
    45 * (if condorcet_qr23_selector_challenger i < condorcet_qr23_selector_member i 0 then 1 else 0) + ∑ k : Fin 3, condorcet_qr23_selector_potential (condorcet_qr23_selector_next i k) := by
  decide +kernel
