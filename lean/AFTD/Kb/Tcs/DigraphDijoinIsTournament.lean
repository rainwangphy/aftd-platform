import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# digraph_dijoin_is_tournament

Topic: graphs   Node: 0e06f0f79364

Provenance: helper lemma. Sanity lemma for digraph_dijoin (arXiv:2610.13798, Sec. 1).

The dijoin of two tournaments is a tournament.
-/

theorem digraph_dijoin_is_tournament {V W : Type*} (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_tournament D₁) (h₂ : digraph_is_tournament D₂) :
    digraph_is_tournament (digraph_dijoin D₁ D₂) := by
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · rcases x with a | a
    · exact h₁.1 a
    · exact h₂.1 a
  · rcases x with a | a <;> rcases y with b | b
    · exact h₁.2 a b (fun h => hxy (by rw [h]))
    · simp [digraph_dijoin]
    · simp [digraph_dijoin]
    · exact h₂.2 a b (fun h => hxy (by rw [h]))
