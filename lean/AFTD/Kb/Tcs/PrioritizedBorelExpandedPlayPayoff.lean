import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385ExpandedPlay
import AFTD.Kb.Tcs.PrioritizedBorelExpandedPlayMaxPriority
import AFTD.Kb.Tcs.PrioritizedBorelExpandedPlayBranchBit
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# prioritized_borel_expanded_play_payoff

Topic: automata   Node: 08ed103abd31

Provenance: helper lemma. Infinite-sequence encoding for arXiv:2611.10136, Conjecture 19.

For every original edge sequence, the phase-game prioritized payoff of its encoded sequence is equivalent to the original prioritized payoff; no legality or strategy consistency is asserted.
-/

theorem prioritized_borel_expanded_play_payoff {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (π : ℕ → TreeGameEdge Q 3) :
    (∃ p : Fin 3,
      Filter.Frequently (fun n => (enc1385ExpandedPlay G π n).prio = p) Filter.atTop ∧
      (∀ q : Fin 3, p < q → ¬ Filter.Frequently (fun n => (enc1385ExpandedPlay G π n).prio = q) Filter.atTop) ∧
      (fun n => (enc1385ExpandedPlay G π n).dir) ∈ (enc1385Game G).winning_sets p) ↔
    (∃ p : Fin 3,
      Filter.Frequently (fun n => (π n).prio = p) Filter.atTop ∧
      (∀ q : Fin 3, p < q → ¬ Filter.Frequently (fun n => (π n).prio = q) Filter.atTop) ∧
      (fun n => (π n).dir) ∈ G.winning_sets p) := by
  have hbranch : (fun n => (enc1385ExpandedPlay G π (n * (Fintype.card Q + 1))).dir) =
      (fun n => (π n).dir) := funext (prioritized_borel_expanded_play_branch_bit G π)
  constructor
  · rintro ⟨p, hf, hm, hw⟩
    have hp := (prioritized_borel_expanded_play_max_priority G π p).mp ⟨hf,hm⟩
    refine ⟨p,hp.1,hp.2,?_⟩
    change (fun n => (enc1385ExpandedPlay G π (n * (Fintype.card Q + 1))).dir) ∈ G.winning_sets p at hw
    rw [hbranch] at hw
    exact hw
  · rintro ⟨p, hf, hm, hw⟩
    have hp := (prioritized_borel_expanded_play_max_priority G π p).mpr ⟨hf,hm⟩
    refine ⟨p,hp.1,hp.2,?_⟩
    change (fun n => (enc1385ExpandedPlay G π (n * (Fintype.card Q + 1))).dir) ∈ G.winning_sets p
    rw [hbranch]
    exact hw
