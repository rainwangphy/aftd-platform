import AFTD.Prelude
import AFTD.Kb.Tcs.Op309IncidenceOverlapFivePeel
import AFTD.Kb.Tcs.Op309GraphFourDegenerate

/-!
# op309_overlap_peel_implies_four_degenerate

Topic: graphs   Node: 6a660850847d

Provenance: helper lemma. OP-309 port-class incidence peeling route, IN-1099.

A common-host graph satisfying the stated overlap-aware incidence peeling rule is four-degenerate.
-/

theorem op309_overlap_peel_implies_four_degenerate{A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (I : SimpleGraph (A ⊕ B)) [DecidableRel I.Adj]
    (Q : SimpleGraph A)
    (hQ : ∀ a a', Q.Adj a a' ↔ a ≠ a' ∧ ∃ b : B,
      I.Adj (.inl a) (.inr b) ∧ I.Adj (.inl a') (.inr b))
    (hpeel : op309_incidence_overlap_five_peel I) : op309_graph_four_degenerate Q := by
  classical
  intro S hS
  obtain ⟨a, ha, hcount, _⟩ := hpeel S hS
  refine ⟨a, ha, S.filter (fun a' => a' ≠ a ∧ ∃ b : B,
    I.Adj (.inl a) (.inr b) ∧ I.Adj (.inl a') (.inr b)), hcount, ?_⟩
  intro a' ha' hadj
  obtain ⟨hne, b, hb, hb'⟩ := (hQ a a').mp hadj
  exact Finset.mem_filter.mpr ⟨ha', hne.symm, b, hb, hb'⟩
