import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsTreeGrundy
import AFTD.Kb.GameTheoryEconomics.TreeMarkableEdges
import AFTD.Kb.GameTheoryEconomics.ArrowsMarkableUnmarked
import AFTD.Kb.GameTheoryEconomics.ArrowsMarkableUnmarkedEmpty
import AFTD.Kb.GameTheoryEconomics.ArrowsMarkableUnmarkedOfLegal
import AFTD.Kb.GameTheoryEconomics.ArrowsPosGrundyEqModTwoOfClass
import AFTD.Kb.GameTheoryEconomics.ArrowsEmptyPos
import AFTD.Kb.GameTheoryEconomics.ArrowsLegalMove
import AFTD.Kb.GameTheoryEconomics.ArrowsPos

/-!
# arrows_parity_of_strategy_class

Topic: combinatorial_games   Node: 30343e61be0d

Provenance: helper lemma. Helper for arrows_parity_of_threads_le_two, arXiv:2610.15145 Theorem 10.3 / Corollary 10.4 (the induction in the proof of Theorem 10.3: every option has value (e-1) mod 2 or an option of value e mod 2), done directly on positions of T without the sum decomposition

Let T be a finite tree and S a class of positions of the Game of Arrows on T that contains the empty position, such that from every position in S with an unmarked markable edge some legal move stays in S, and every legal move from a position in S lands in S or admits a legal reply back into S. Then the Grundy value of the Game of Arrows on T equals the number of markable edges of T modulo 2.
-/

theorem arrows_parity_of_strategy_class {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (S : ArrowsPos V → Prop)
    (h0 : S (ArrowsEmptyPos V))
    (hex : ∀ p, S p → 1 ≤ arrows_markable_unmarked T p → ∃ q, ArrowsLegalMove T p q ∧ S q)
    (hcl : ∀ p q, S p → ArrowsLegalMove T p q → S q ∨ ∃ r, ArrowsLegalMove T q r ∧ S r) :
    arrows_tree_grundy T = tree_markable_edges T % 2 := by
  classical
  rw [← arrows_markable_unmarked_empty T]
  apply arrows_pos_grundy_eq_mod_two_of_class T S _ (arrows_markable_unmarked_of_legal T) hex hcl _ _ h0
  have hne : Nonempty V := hT.1.nonempty
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  have h1 : arrows_markable_unmarked T (ArrowsEmptyPos V) ≤ T.edgeFinset.card := by
    unfold arrows_markable_unmarked; exact Finset.card_filter_le _ _
  have h2 := T.card_edgeFinset_le_card_choose_two
  rw [Nat.choose_two_right] at h2
  have h3 : Fintype.card V * (Fintype.card V - 1) / 2 ≤ Fintype.card V * (Fintype.card V - 1) :=
    Nat.div_le_self _ _
  have h4 : Fintype.card V * (Fintype.card V - 1) < Fintype.card V * Fintype.card V :=
    Nat.mul_lt_mul_of_pos_left (by omega) hpos
  omega
