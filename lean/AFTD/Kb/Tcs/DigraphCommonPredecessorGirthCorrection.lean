import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_common_predecessor_girth_correction

Topic: graphs   Node: 8b0a4c9831a4

Provenance: helper lemma. Girth-dependent center budget for the four-cycle campaign.

The sum, over common-predecessor edges of multiplicity at least two, of the positive part of g+1 minus twice the number of common predecessors.
-/

noncomputable def digraph_common_predecessor_girth_correction
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] (g : ℕ) : ℕ := by
  classical
  exact ∑ e ∈ (digraph_common_predecessor_graph D).edgeFinset.filter
      (fun e => 2 ≤ (Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x).card),
    (g + 1 - 2 * (Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x).card)
