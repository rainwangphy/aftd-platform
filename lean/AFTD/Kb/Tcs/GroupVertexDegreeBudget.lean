import AFTD.Prelude

/-!
# group_vertex_degree_budget

Topic: graphs   Node: 57a2810bc42e

Provenance: helper lemma. OP-1957; graph-to-count transfer for the deleted-four-block matching obstruction.

A vertex whose neighbors lie in its group, separator or outside pool has the displayed degree budget.
-/

set_option maxHeartbeats 2000000

theorem group_vertex_degree_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F S T : Finset V) (v : V) (hv : v ∈ F)
    (hcover : ∀ w, G.Adj v w → w ∈ F ∨ w ∈ S ∨ w ∈ T) :
    (G.neighborFinset v).card + 1 ≤ F.card + S.card + T.card := by
  classical
  have hsub : G.neighborFinset v ⊆ F.erase v ∪ S ∪ T := by
    intro w hw
    have hadj : G.Adj v w := by simpa only [SimpleGraph.mem_neighborFinset] using hw
    rcases hcover w hadj with hF | hS | hT
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨(G.ne_of_adj hadj).symm,hF⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hS)
    · exact Finset.mem_union_right _ hT
  have hcard := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (F.erase v ∪ S) T
  have hu2 := Finset.card_union_le (F.erase v) S
  have he := Finset.card_erase_add_one hv
  omega
