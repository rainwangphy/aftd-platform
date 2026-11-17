import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# enc1385ExpandedPlay

Topic: automata   Node: c3ff7de03023

Provenance: helper lemma. Infinite-sequence encoding for arXiv:2611.10136, Conjecture 19.

Expand an arbitrary sequence of original edges into phase-game edges by indexing its fixed-length direction-and-state blocks. This definition alone does not assert that the expanded sequence is a legal play.
-/

noncomputable def enc1385ExpandedPlay {Q : Type} [Fintype Q]
    (G : PrioritizedBorelGame Q 3) (π : ℕ → TreeGameEdge Q 3) (n : ℕ) :
    TreeGameEdge (Enc1385State Q) 3 :=
  let L := Fintype.card Q + 1
  let e := π (n / L)
  let i := n % L
  let bit := (enc1385Block e).getD i false
  let prio := if i = Fintype.card Q then e.prio else 0
  let node := List.ofFn (fun j : Fin n =>
    (enc1385Block (π (j.val / L))).getD (j.val % L) false)
  let phase : Enc1385State Q := ⟨e.source_node,e.source_state,(enc1385Block e).take i⟩
  ⟨node, phase, bit, prio, enc1385Step G phase bit⟩
