import AFTD.Prelude
import AFTD.Kb.Tcs.CopsCanWinFrom
import AFTD.Kb.Tcs.HasCopWinStrategy

/-!
# cop_win_two_of_dominating_pair

Topic: graphs   Node: 668443399d68

Provenance: helper lemma. step towards op_292_cop_number_p7_claw_free

A graph admitting a 2-vertex dominating set has a winning strategy for 2 cops.
-/

/-- A graph admitting a 2-vertex dominating set has a winning strategy for 2 cops. -/
theorem cop_win_two_of_dominating_pair {V : Type*} (G : SimpleGraph V) (u v : V)
    (hdom : ∀ w : V, w = u ∨ w = v ∨ G.Adj u w ∨ G.Adj v w) :
    HasCopWinStrategy G 2 := by
  let C₀ : Fin 2 → V := fun i => if i = 0 then u else v
  use C₀
  intro R
  rcases hdom R with hu | hv | hadj_u | hadj_v
  · apply CopsCanWinFrom.capture
    exact ⟨0, hu.symm⟩
  · apply CopsCanWinFrom.capture
    exact ⟨1, hv.symm⟩
  · let C' : Fin 2 → V := fun i => if i = 0 then R else v
    apply CopsCanWinFrom.step_capture C₀ R C'
    · intro i
      fin_cases i
      · right; exact hadj_u
      · left; rfl
    · exact ⟨0, rfl⟩
  · let C' : Fin 2 → V := fun i => if i = 0 then u else R
    apply CopsCanWinFrom.step_capture C₀ R C'
    · intro i
      fin_cases i
      · left; rfl
      · right; exact hadj_v
    · exact ⟨1, rfl⟩
