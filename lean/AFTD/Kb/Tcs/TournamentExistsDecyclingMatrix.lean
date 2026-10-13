import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentMinRank
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphIsAcyclicOfRank
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.DigraphFlipByMatrix

/-!
# tournament_exists_decycling_matrix

Topic: graphs   Node: 03c2d02c0759

Provenance: helper lemma. Helper for the bounds on tournament minimum rank in arXiv:2610.13798, Sec. 2.2: the minimum defining tmr(D) is over a nonempty set.

Every finite tournament has a symmetric decycling matrix over F₂ (so its minimum rank is attained).
-/

theorem tournament_exists_decycling_matrix (V : Type) [Fintype V] (D : Digraph V)
    (h : digraph_is_tournament D) :
    ∃ M : Matrix V V (ZMod 2), M.IsSymm ∧ digraph_is_acyclic (digraph_flip_by_matrix D M) := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let M : Matrix V V (ZMod 2) := fun x y =>
    if (D.Adj x y ∧ e y < e x) ∨ (D.Adj y x ∧ e x < e y) then 1 else 0
  refine ⟨M, Matrix.IsSymm.ext (fun i j => ?_), ?_⟩
  · by_cases h1 : D.Adj i j ∧ e j < e i <;> by_cases h2 : D.Adj j i ∧ e i < e j <;>
      simp [M, h1, h2]
  · apply digraph_is_acyclic_of_rank _ (fun v => (e v : ℕ))
    intro x y hxy
    have hxy' : x ≠ y := by
      rintro rfl
      rcases hxy with ⟨_, h'⟩ | ⟨_, h'⟩ <;> exact h.1 x h'
    have hne : e x ≠ e y := fun h' => hxy' (e.injective h')
    suffices hlt : e x < e y by exact hlt
    rcases hxy with ⟨hM, hA⟩ | ⟨hM, hA⟩
    · simp only [M] at hM
      split_ifs at hM with hc
      · rcases hc with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact absurd hA ((h.2 x y hxy').1 h1)
        · exact h2
      · exact absurd hM (by decide)
    · simp only [M] at hM
      split_ifs at hM with hc
      · exact absurd rfl hM
      · push_neg at hc
        exact lt_of_le_of_ne (hc.1 hA) hne
