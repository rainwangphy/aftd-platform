import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickGameMoveZero
import AFTD.Kb.GameTheoryEconomics.PickGameMovePayoff

/-!
# pick_game_is_spe

Topic: fair_division   Node: 79212b8eddff

Provenance: helper lemma. Operational finite perfect-information picking game for arXiv:2611.09685 Section 7, OP-1323.

An outcome-continuation function is subgame-perfect for a fixed finite two-agent picking order if, after every duplicate-free history, its agent-0 continuation is contained in the available objects, and either there are none and it is empty, or an available object induces that continuation and gives the current picker at least as much additive utility as every alternative followed by the specified continuation. The order has one turn per object. Histories include all off-path subgames.
-/

noncomputable def pick_game_is_spe {n : ℕ} (u : Fin 2 → Fin n → ℝ)
    (s : List (Fin 2)) (F : List (Fin n) → Finset (Fin n)) : Prop := s.length = n ∧ ∀ h : List (Fin n), h.Nodup →
    let R := Finset.univ \ h.toFinset
    F h ⊆ R ∧
    if R.Nonempty then
      ∃ x ∈ R, F h = pick_game_move_zero s F h x ∧
        ∀ y ∈ R, pick_game_move_payoff u s F h y ≤ pick_game_move_payoff u s F h x
    else F h = ∅
