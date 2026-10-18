import AFTD.Prelude
import AFTD.Kb.Tcs.NusMinCard
import AFTD.Kb.Tcs.FinsetHasNoUniqueSumsUnivZmod
import AFTD.Kb.Tcs.FinsetIsMidpointBalancedOfHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetCardGeOneAddClogOfMidpointBalanced
import AFTD.Kb.Tcs.FinsetIsMidpointBalanced
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums

/-!
# nus_min_card_ge_one_add_clog

Topic: combinatorics   Node: ca00e02feda1

Provenance: formalization of a published result. Source: arXiv:2610.09349 (A near-quadratic lower bound for sets with no unique sums), Appendix B (the lower bound 1 + ⌈log₂ p⌉ ≤ m(p), from Lemma B.1).

For an odd prime p, m(p) ≥ 1 + ⌈log₂ p⌉: every subset of Z/pZ with no unique sums has at least 1 + ⌈log₂ p⌉ elements.
-/

theorem nus_min_card_ge_one_add_clog {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    1 + Nat.clog 2 p ≤ nus_min_card p := by
  unfold nus_min_card
  apply le_csInf
  · refine ⟨(Finset.univ : Finset (ZMod p)).card, ⟨Finset.univ, finset_has_no_unique_sums_univ_zmod hp, rfl⟩⟩
  · rintro b ⟨A, hA, rfl⟩
    have h_bal := finset_is_midpoint_balanced_of_has_no_unique_sums hp A hA
    exact finset_card_ge_one_add_clog_of_midpoint_balanced A h_bal
