import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentCutAddCutComplEqSumOutCount
import AFTD.Kb.Tcs.TournamentCutCountSelfEqChooseTwo
import AFTD.Kb.Tcs.DigraphCutCount
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphOutCount

/-!
# tournament_cut_count_eq_sub

Topic: graphs   Node: e6273a0f14e7

Provenance: helper lemma. arXiv:2610.40521 Lemma 2, Equation (1)

In any tournament T on vertex set Fin n and for any subset S of vertices, the directed cut size from S to its complement Sᶜ equals the sum of the outdegrees of vertices in S minus Nat.choose S.card 2.
-/

open Classical in
/-- Directed cut size c_T(S) equals the sum of outdegrees in S minus (|S| choose 2). -/
lemma tournament_cut_count_eq_sub (n : ℕ) (T : Digraph (Fin n))
    (hT : digraph_is_tournament T) (S : Finset (Fin n)) :
    digraph_cut_count T S Sᶜ = (∑ v ∈ S, digraph_out_count T v) - Nat.choose S.card 2 := by
  have h1 := tournament_cut_add_cut_compl_eq_sum_out_count n T S
  have h2 := tournament_cut_count_self_eq_choose_two n T hT S
  omega
