import AFTD.Prelude
import AFTD.Kb.Tcs.TernaryLineCoverCardGe

/-!
# bicirculant_card

Topic: graphs   Node: 5ef7c90993ec

Provenance: helper lemma. folklore

For any positive modulus m and any connection subsets R, S, T of ZMod m, the vertex set (Fin 2) × (ZMod m) of the bicirculant graph has cardinality 2 * m.
-/

/-- The vertex set (Fin 2) × (ZMod m) of a bicirculant graph on ZMod m has cardinality 2 * m. -/
theorem bicirculant_card (m : ℕ) [NeZero m] (R S T : Finset (ZMod m)) : Fintype.card (Fin 2 × ZMod m) = 2 * m := by first | exact ternary_line_cover_card_ge | (apply ternary_line_cover_card_ge <;> assumption) | (apply ternary_line_cover_card_ge <;> simp_all) | simpa using ternary_line_cover_card_ge
