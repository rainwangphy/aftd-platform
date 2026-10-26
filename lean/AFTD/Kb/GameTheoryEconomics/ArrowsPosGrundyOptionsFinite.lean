import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPosGrundy
import AFTD.Kb.GameTheoryEconomics.ArrowsLegalMove
import AFTD.Kb.GameTheoryEconomics.ArrowsPos

/-!
# arrows_pos_grundy_options_finite

Topic: combinatorial_games   Node: a0abcacc85bf

Provenance: helper lemma. Helper for arrows_parity_of_threads_le_two, arXiv:2610.15145 Theorem 10.3 / Corollary 10.4 (the induction in the proof of Theorem 10.3: every option has value (e-1) mod 2 or an option of value e mod 2), done directly on positions of T without the sum decomposition

For any fuel and position p of the Game of Arrows on a finite graph, the set of fuel-bounded Grundy values of the legal options of p is finite.
-/

theorem arrows_pos_grundy_options_finite {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (p : ArrowsPos V) :
    { m : ℕ | ∃ q, ArrowsLegalMove G p q ∧ m = arrows_pos_grundy G n q }.Finite := by
  have : Finite (ArrowsPos V) := by unfold ArrowsPos; infer_instance
  exact (Set.finite_range (fun q : ArrowsPos V => arrows_pos_grundy G n q)).subset
    (by rintro _ ⟨q, -, rfl⟩; exact ⟨q, rfl⟩)
