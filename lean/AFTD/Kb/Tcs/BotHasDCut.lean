import AFTD.Prelude
import AFTD.Kb.Tcs.GraphHasDCut
import AFTD.Kb.Tcs.GraphIsDCut

/-!
# bot_has_d_cut

Topic: graphs   Node: ce995e2bc1be

Provenance: helper lemma. arXiv:2611.26556 Section 1

For any finite vertex type with at least two vertices and any d, the empty simple graph has a d-cut.
-/

/-- The empty graph on at least two vertices has a d-cut for any d. -/
lemma bot_has_d_cut {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 2 ≤ Fintype.card V) (d : ℕ) :
    graph_has_d_cut (⊥ : SimpleGraph V) d := by
  classical
  have hpos : 0 < Fintype.card V := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp hpos
  obtain ⟨x⟩ := ‹Nonempty V›
  obtain ⟨y, hyx⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) x
  refine ⟨{x}, ?_, ?_, ?_, ?_⟩
  · simp
  · refine ⟨y, ?_⟩
    simp [Finset.mem_compl, hyx]
  · intro u hu
    simp
  · intro v hv
    simp
