import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_not_king_of_covered

Topic: graphs   Node: 146343d584af

Provenance: formalization of a published result. Source: arXiv:2610.40521 Observation 4

If a vertex w covers another vertex v in a tournament T (that is, w -> v and w -> x for every out-neighbor x of v), then v is not a king in T.
-/

/-- If a vertex w covers v in a tournament T, then v is not a king in T. -/
theorem tournament_not_king_of_covered {V : Type*} (T : Digraph V)
    (hT : digraph_is_tournament T) (w v : V)
    (hcov : T.Adj w v ∧ ∀ x, T.Adj v x → T.Adj w x) :
    ¬ (∀ u, u ≠ v → T.Adj v u ∨ ∃ w', T.Adj v w' ∧ T.Adj w' u) := by
  intro h
  obtain ⟨hwv, hcovx⟩ := hcov
  have hirr : ∀ x, ¬ T.Adj x x := hT.1
  have htour : ∀ x y, x ≠ y → (T.Adj x y ↔ ¬ T.Adj y x) := hT.2
  have hwv_ne : w ≠ v := fun heq => hirr v (heq ▸ hwv)
  have hv_ne_w : v ≠ w := fun heq => hwv_ne heq.symm
  rcases h w hwv_ne with hvw | ⟨x, hvx, hxw⟩
  · exact (htour v w hv_ne_w).mp hvw hwv
  · have hwx : T.Adj w x := hcovx x hvx
    have hx_ne_w : x ≠ w := fun heq => hirr x (heq ▸ hxw)
    exact (htour x w hx_ne_w).mp hxw hwx
