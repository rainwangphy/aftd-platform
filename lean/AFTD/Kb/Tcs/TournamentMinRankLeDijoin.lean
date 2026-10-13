import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentMinRank
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.TournamentExistsDecyclingMatrix
import AFTD.Kb.Tcs.DigraphDijoinIsTournament
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.DigraphFlipByMatrix
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_min_rank_le_dijoin

Topic: graphs   Node: 75b83bd3857d

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Observation 2.3 (stated here for the two sides of a dijoin; the average bound follows from the max).

For finite tournaments D₁, D₂: tmr(D₁ → D₂) ≥ max(tmr(D₁), tmr(D₂)) (hence ≥ (tmr(D₁) + tmr(D₂))/2), because the principal submatrix of a decycling matrix on an induced subtournament decycles it and has no larger rank.
-/

theorem tournament_min_rank_le_dijoin
    (V W : Type) [Fintype V] [Fintype W] (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_tournament D₁) (h₂ : digraph_is_tournament D₂) :
    max (tournament_min_rank D₁) (tournament_min_rank D₂) ≤
      tournament_min_rank (digraph_dijoin D₁ D₂) := by
  obtain ⟨M0, hM0s, hM0a⟩ := tournament_exists_decycling_matrix (V ⊕ W) _
    (digraph_dijoin_is_tournament D₁ D₂ h₁ h₂)
  have hne : Set.Nonempty {r | ∃ M : Matrix (V ⊕ W) (V ⊕ W) (ZMod 2), M.IsSymm ∧
      digraph_is_acyclic (digraph_flip_by_matrix (digraph_dijoin D₁ D₂) M) ∧ M.rank = r} :=
    ⟨_, M0, hM0s, hM0a, rfl⟩
  obtain ⟨M, hMs, hMa, hMr⟩ := Nat.sInf_mem hne
  have lower : ∀ (U : Type) [Fintype U] (f : U → V ⊕ W) (D : Digraph U),
      (∀ a b, (digraph_dijoin D₁ D₂).Adj (f a) (f b) ↔ D.Adj a b) →
      tournament_min_rank D ≤ tournament_min_rank (digraph_dijoin D₁ D₂) := by
    intro U _ f D hD
    have step : ∀ x y, (digraph_flip_by_matrix D (M.submatrix f f)).Adj x y →
        (digraph_flip_by_matrix (digraph_dijoin D₁ D₂) M).Adj (f x) (f y) := by
      intro x y hxy
      simp only [digraph_flip_by_matrix, Matrix.submatrix_apply, hD] at hxy ⊢
      exact hxy
    have hac : digraph_is_acyclic (digraph_flip_by_matrix D (M.submatrix f f)) := by
      intro a ha
      apply hMa (f a)
      have key : ∀ x y, Relation.TransGen (digraph_flip_by_matrix D (M.submatrix f f)).Adj x y →
          Relation.TransGen (digraph_flip_by_matrix (digraph_dijoin D₁ D₂) M).Adj (f x) (f y) := by
        intro x y hxy
        induction hxy with
        | single h => exact .single (step _ _ h)
        | tail _ h ih => exact .tail ih (step _ _ h)
      exact key a a ha
    calc tournament_min_rank D ≤ (M.submatrix f f).rank :=
          Nat.sInf_le ⟨M.submatrix f f, hMs.submatrix f, hac, rfl⟩
      _ ≤ M.rank := Matrix.rank_submatrix_le _ _ _
      _ = _ := hMr
  apply max_le
  · exact lower V Sum.inl D₁ (fun a b => Iff.rfl)
  · exact lower W Sum.inr D₂ (fun a b => Iff.rfl)
