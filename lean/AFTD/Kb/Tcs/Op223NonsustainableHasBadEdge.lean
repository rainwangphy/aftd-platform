import AFTD.Prelude
import AFTD.Kb.Tcs.IsNonsustainableTree
import AFTD.Kb.Tcs.IsSustainableEdge
import AFTD.Kb.Tcs.IsSustainableTree

/-!
# op223_nonsustainable_has_bad_edge

Topic: graphs   Node: 73f8141af00a

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1

Every nonsustainable finite tree contains an edge that is not sustainable.
-/

open SimpleGraph

theorem op223_nonsustainable_has_bad_edge {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : is_nonsustainable_tree T) :
    ∃ u v : V, T.Adj u v ∧ ¬ is_sustainable_edge T s(u, v) := by
  classical
  have hbad : ¬ ∀ e ∈ T.edgeSet, is_sustainable_edge T e := by
    intro h
    exact hT.2 ⟨hT.1, h⟩
  push_neg at hbad
  obtain ⟨e, he, hnot⟩ := hbad
  induction e using Sym2.ind with
  | _ u v => exact ⟨u, v, he, hnot⟩
