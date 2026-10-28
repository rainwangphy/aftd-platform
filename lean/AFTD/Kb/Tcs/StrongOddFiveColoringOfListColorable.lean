import AFTD.Prelude
import AFTD.Kb.Tcs.IsStrongOddColoring
import AFTD.Kb.Tcs.IsStrongOddListColorable

/-!
# strong_odd_five_coloring_of_list_colorable

Topic: graphs   Node: a22908a069c0

Provenance: original. Related work: arXiv:2610.34874

If a finite simple graph is strongly odd 5-list-colorable, then it admits an ordinary strong odd 5-coloring.
-/

/-- Strong odd 5-list-colorability implies ordinary strong odd 5-colorability. -/
theorem strong_odd_five_coloring_of_list_colorable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : is_strong_odd_list_colorable G 5) :
    ∃ f : V → Fin 5, is_strong_odd_coloring G f := by
  obtain ⟨f, -, hf⟩ := h (Fin 5) (fun _ => Finset.univ) (fun _ => by simp)
  exact ⟨f, hf⟩
