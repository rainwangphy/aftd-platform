import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetQr23SelectorMember
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# condorcet_qr23_selector_complete

Topic: social_choice   Node: 37f15a774d06

Provenance: helper lemma. Certificate data for condorcet_tournament_stationary_restriction_obstruction (restriction diagnostic for OP-19 on the quadratic-residue tournament modulo 23; potential from experiment 8584, recomputed by CP-SAT). Related definition from Condorcet winning sets, Social Choice and Welfare 44(3):493-517 (2015).

Every three-element subset of Fin 23 is the member set of some indexed triple.
-/

private def condorcet_qr23_selector_complete_rank (a b c : Fin 23) : Fin 1771 :=
  ⟨(1771 - (23 - a.val) * (22 - a.val) * (21 - a.val) / 6 + (22 - a.val) * (21 - a.val) / 2
    - (23 - b.val) * (22 - b.val) / 2 + c.val - b.val - 1) % 1771, Nat.mod_lt _ (by decide)⟩

private theorem condorcet_qr23_selector_complete_rank_spec : ∀ a b c : Fin 23, a < b → b < c →
    condorcet_qr23_selector_member (condorcet_qr23_selector_complete_rank a b c) 0 = a ∧ condorcet_qr23_selector_member (condorcet_qr23_selector_complete_rank a b c) 1 = b ∧
      condorcet_qr23_selector_member (condorcet_qr23_selector_complete_rank a b c) 2 = c := by
  decide +kernel

theorem condorcet_qr23_selector_complete : ∀ T : Finset (Fin 23), T.card = 3 →
    ∃ i, ({condorcet_qr23_selector_member i 0, condorcet_qr23_selector_member i 1, condorcet_qr23_selector_member i 2} : Finset (Fin 23)) = T := by
  intro T hT
  have key : ∀ a b c : Fin 23, a < b → b < c →
      ∃ i, ({condorcet_qr23_selector_member i 0, condorcet_qr23_selector_member i 1, condorcet_qr23_selector_member i 2} : Finset (Fin 23)) = {a, b, c} := by
    intro a b c hab hbc
    obtain ⟨h0, h1, h2⟩ := condorcet_qr23_selector_complete_rank_spec a b c hab hbc
    exact ⟨_, by rw [h0, h1, h2]⟩
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hT
  have e1 : ∀ p q r : Fin 23, ({p, q, r} : Finset (Fin 23)) = {p, r, q} := fun p q r => by
    rw [Finset.pair_comm]
  have e2 : ∀ p q r : Fin 23, ({p, q, r} : Finset (Fin 23)) = {q, p, r} := fun p q r =>
    Finset.insert_comm p q {r}
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  · obtain ⟨i, hi⟩ := key x y z h1 h3; exact ⟨i, hi⟩
  · obtain ⟨i, hi⟩ := key x z y h2 h3; exact ⟨i, hi.trans (e1 x z y)⟩
  · exact absurd (h1.trans h3) (not_lt.mpr h2.le)
  · obtain ⟨i, hi⟩ := key z x y h2 h1
    exact ⟨i, hi.trans ((e2 z x y).trans (e1 x z y))⟩
  · obtain ⟨i, hi⟩ := key y x z h1 h2; exact ⟨i, hi.trans (e2 y x z)⟩
  · exact absurd (h3.trans h1) (not_lt.mpr h2.le)
  · obtain ⟨i, hi⟩ := key y z x h3 h2
    exact ⟨i, hi.trans ((e1 y z x).trans (e2 y x z))⟩
  · obtain ⟨i, hi⟩ := key z y x h3 h1
    exact ⟨i, hi.trans ((e2 z y x).trans ((e1 y z x).trans (e2 y x z)))⟩
