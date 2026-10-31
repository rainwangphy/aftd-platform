import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentCutCountEqSub
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphCutCount
import AFTD.Kb.Tcs.DigraphOutCount

/-!
# tournament_directed_cut_eq_of_outdegrees_eq

Topic: graphs   Node: 6c4b494ee573

Provenance: formalization of a published result. Source: arXiv:2610.40521 Lemma 2: Directed Cut-Query Complexity of Finding a King

Let T₁ and T₂ be tournaments on vertex set Fin n such that every vertex v has the same outdegree in T₁ and T₂. Then for every subset S ⊆ Fin n, the number of edges directed from S to its complement in T₁ equals that in T₂.
-/

open Classical in
/-- Directed cut sizes in tournaments depend only on vertex outdegrees. -/
theorem tournament_directed_cut_eq_of_outdegrees_eq (n : ℕ)
    (T₁ T₂ : Digraph (Fin n)) (hT₁ : digraph_is_tournament T₁) (hT₂ : digraph_is_tournament T₂)
    (hdeg : ∀ v : Fin n, digraph_out_count T₁ v = digraph_out_count T₂ v)
    (S : Finset (Fin n)) :
    digraph_cut_count T₁ S Sᶜ = digraph_cut_count T₂ S Sᶜ := by
  rw [tournament_cut_count_eq_sub n T₁ hT₁ S, tournament_cut_count_eq_sub n T₂ hT₂ S]
  simp_rw [hdeg]
