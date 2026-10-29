import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorMember
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorChallenger

/-!
# condorcet_qr23_selector_chk

Topic: social_choice   Node: b22653b86277

Provenance: helper lemma. Certificate data for condorcet_tournament_stationary_restriction_obstruction (restriction diagnostic for OP-19 on the quadratic-residue tournament modulo 23; potential from experiment 8584, recomputed by CP-SAT). Related definition from Condorcet winning sets, Social Choice and Welfare 44(3):493-517 (2015).

Each indexed triple is listed in increasing order, its challenger is outside it, and the challenger beats every member in the quadratic-residue tournament modulo 23.
-/

theorem condorcet_qr23_selector_chk : ∀ i : Fin 1771,
    condorcet_qr23_selector_member i 0 < condorcet_qr23_selector_member i 1 ∧ condorcet_qr23_selector_member i 1 < condorcet_qr23_selector_member i 2 ∧
      condorcet_qr23_selector_challenger i ≠ condorcet_qr23_selector_member i 0 ∧ condorcet_qr23_selector_challenger i ≠ condorcet_qr23_selector_member i 1 ∧ condorcet_qr23_selector_challenger i ≠ condorcet_qr23_selector_member i 2 ∧
      ∀ k : Fin 3, ((condorcet_qr23_selector_member i k).val + 23 - (condorcet_qr23_selector_challenger i).val) % 23 ∈ [1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18] := by
  decide +kernel
