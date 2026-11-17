import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385ExpandedPlay
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# prioritized_borel_expanded_play_node_adjacency

Topic: automata   Node: f19bb1ac463c

Provenance: helper lemma. Infinite-play encoding for arXiv:2611.10136, Conjecture 19.

For any original edge sequence, consecutive encoded edges have matching tree-node endpoints; this assertion alone does not establish state adjacency or edge legality.
-/

theorem prioritized_borel_expanded_play_node_adjacency {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (π : ℕ → TreeGameEdge Q 3) (n : ℕ) :
    (enc1385ExpandedPlay G π (n+1)).source_node =
      (enc1385ExpandedPlay G π n).source_node ++ [(enc1385ExpandedPlay G π n).dir] := by
  simpa [enc1385ExpandedPlay, List.concat_eq_append] using
    (List.ofFn_succ' (fun i : Fin (n+1) =>
      (enc1385Block (π (i.val / (Fintype.card Q + 1)))).getD
        (i.val % (Fintype.card Q + 1)) false))
