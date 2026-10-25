import AFTD.Prelude
import AFTD.Kb.Tcs.GhzMatchingCrossCutCardParity
import AFTD.Kb.Tcs.GhzIsPerfectMatching

/-!
# ghz_matching_cross_cut_ge_two_of_even

Topic: quantum   Node: 58480b63fa34

Provenance: helper lemma. arXiv:2610.22190 Section 4

For any finite type V with decidable equality, simple graph G on V, perfect matching M of G, and subset S ⊆ V of even cardinality, if M contains at least one edge crossing the cut between S and Sᶜ, then M contains at least 2 edges crossing the cut.
-/

/-- A perfect matching crossing an even cut must contain at least two crossing edges. -/
lemma ghz_matching_cross_cut_ge_two_of_even {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (M : Finset (Sym2 V)) (hM : ghz_is_perfect_matching G M)
    (S : Finset V) (heven : S.card % 2 = 0)
    (hcross : (M.filter (fun e => ∃ u ∈ S, ∃ v ∈ (Sᶜ : Finset V), e = s(u, v))).card ≠ 0) :
    2 ≤ (M.filter (fun e => ∃ u ∈ S, ∃ v ∈ (Sᶜ : Finset V), e = s(u, v))).card := by
  have hparity := ghz_matching_cross_cut_card_parity G M hM S
  omega
