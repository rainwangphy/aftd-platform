import AFTD.Prelude
import AFTD.Kb.Tcs.CopsCanWinFrom

/-!
# HasCopWinStrategy

Topic: graphs   Node: 9eb395dcaba7

Provenance: formalization of a published result. Source: arXiv:2610.20129 Sec. 1

The cop player has a winning strategy with c cops on G if there exists an initial placement of cops from which the cops can capture the robber against any initial placement of the robber.
-/

/-- The cop player has a winning strategy with c cops on G. -/
def HasCopWinStrategy {V : Type*} (G : SimpleGraph V) (c : ℕ) : Prop := ∃ C₀ : Fin c → V, ∀ R₀ : V, CopsCanWinFrom G c C₀ R₀
