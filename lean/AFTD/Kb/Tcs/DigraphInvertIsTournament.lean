import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphInvert
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# digraph_invert_is_tournament

Topic: graphs   Node: a7f6ed12c1c9

Provenance: helper lemma. Sanity lemma for digraph_invert and digraph_is_tournament (arXiv:2610.13798, Sec. 1).

Inverting a vertex set of a tournament gives a tournament.
-/

theorem digraph_invert_is_tournament {V : Type*} (D : Digraph V) (X : Set V)
    (hD : digraph_is_tournament D) : digraph_is_tournament (digraph_invert D X) := by
  obtain ⟨h1, h2⟩ := hD
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · simp only [digraph_invert]; have := h1 x; tauto
  · simp only [digraph_invert]
    have := h2 x y hxy; have := h2 y x (Ne.symm hxy)
    by_cases hx : x ∈ X <;> by_cases hy : y ∈ X <;> simp [hx, hy] <;> tauto
