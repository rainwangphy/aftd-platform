import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorMember
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorChallenger
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorNext

/-!
# condorcet_qr23_selector_trans_lo

Topic: social_choice   Node: ab95bd5bd7dd

Provenance: helper lemma. Certificate data for condorcet_tournament_stationary_restriction_obstruction (restriction diagnostic for OP-19 on the quadratic-residue tournament modulo 23; potential from experiment 8584, recomputed by CP-SAT). Related definition from Condorcet winning sets, Social Choice and Welfare 44(3):493-517 (2015).

For the first 886 triples, each transition's member list is the old triple with the evicted member replaced by the challenger (as sets of members).
-/

theorem condorcet_qr23_selector_trans_lo : ∀ i : Fin 1771, i.val < 886 →
    ∀ k : Fin 3,
      (∀ m : Fin 3, condorcet_qr23_selector_member (condorcet_qr23_selector_next i k) m = condorcet_qr23_selector_challenger i ∨ (condorcet_qr23_selector_member (condorcet_qr23_selector_next i k) m ≠ condorcet_qr23_selector_member i k ∧
        (condorcet_qr23_selector_member i 0 = condorcet_qr23_selector_member (condorcet_qr23_selector_next i k) m ∨ condorcet_qr23_selector_member i 1 = condorcet_qr23_selector_member (condorcet_qr23_selector_next i k) m ∨ condorcet_qr23_selector_member i 2 = condorcet_qr23_selector_member (condorcet_qr23_selector_next i k) m))) ∧
      (condorcet_qr23_selector_challenger i = condorcet_qr23_selector_member (condorcet_qr23_selector_next i k) 0 ∨ condorcet_qr23_selector_challenger i = condorcet_qr23_selector_member (condorcet_qr23_selector_next i k) 1 ∨ condorcet_qr23_selector_challenger i = condorcet_qr23_selector_member (condorcet_qr23_selector_next i k) 2) ∧
      (∀ m : Fin 3, m ≠ k → (condorcet_qr23_selector_member i m = condorcet_qr23_selector_member (condorcet_qr23_selector_next i k) 0 ∨ condorcet_qr23_selector_member i m = condorcet_qr23_selector_member (condorcet_qr23_selector_next i k) 1 ∨ condorcet_qr23_selector_member i m = condorcet_qr23_selector_member (condorcet_qr23_selector_next i k) 2)) := by
  decide +kernel
