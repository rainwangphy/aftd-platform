import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReverse
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# digraph_reverse_is_tournament

Topic: graphs   Node: e926ab691930

Provenance: helper lemma. Sanity lemma for digraph_reverse (arXiv:2610.13798, Sec. 4).

The reverse of a tournament is a tournament.
-/

theorem digraph_reverse_is_tournament {V : Type*} (D : Digraph V)
    (h : digraph_is_tournament D) : digraph_is_tournament (digraph_reverse D) :=
  ⟨fun x => h.1 x, fun x y hxy => h.2 y x (Ne.symm hxy)⟩
