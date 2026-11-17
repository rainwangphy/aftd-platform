import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385ExpandedPlay
import AFTD.Kb.Tcs.PrioritizedBorelPaddingOffsetMaxPriority
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.TreeGameEdge

/-!
# prioritized_borel_expanded_play_max_priority

Topic: automata   Node: 579392e6396d

Provenance: helper lemma. Infinite-sequence encoding for arXiv:2611.10136, Conjecture 19.

The encoded sequence has exactly the same maximal recurring priority as the original edge sequence.
-/

theorem prioritized_borel_expanded_play_max_priority {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (π : ℕ → TreeGameEdge Q 3) (p : Fin 3) :
    (Filter.Frequently (fun n => (enc1385ExpandedPlay G π n).prio = p) Filter.atTop ∧
      ∀ q : Fin 3, p < q → ¬ Filter.Frequently (fun n => (enc1385ExpandedPlay G π n).prio = q) Filter.atTop) ↔
    (Filter.Frequently (fun n => (π n).prio = p) Filter.atTop ∧
      ∀ q : Fin 3, p < q → ¬ Filter.Frequently (fun n => (π n).prio = q) Filter.atTop) := by
  simpa [enc1385ExpandedPlay] using
    (prioritized_borel_padding_offset_max_priority (Fintype.card Q + 1) (Fintype.card Q)
      (by omega) (fun n => (π n).prio) p)
