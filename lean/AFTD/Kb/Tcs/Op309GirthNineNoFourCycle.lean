import AFTD.Prelude

/-!
# op309_girth_nine_no_four_cycle

Topic: graphs   Node: 7d3a4e180183

Provenance: helper lemma. OP-309 girth-nine canonical-port local cycle exclusions.

A graph of girth at least nine has no cycle of length 4 on distinct vertices.
-/

theorem op309_girth_nine_no_four_cycle
    {V : Type*} (G : SimpleGraph V) (hgirth : (9 : ℕ∞) ≤ G.egirth)
    (a b c d : V) (hvertices : [a,b,c,d].Nodup)
    (hedges : G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) : False := by
  rcases hedges with ⟨hab, hbc, hcd, hda⟩
  let w : G.Walk a a := SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))
  have hw : w.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, by norm_num [w]⟩
    rw [SimpleGraph.Walk.isPath_def]
    change [b, c, d, a].Nodup
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true] at hvertices ⊢
    tauto
  have hle : G.egirth ≤ (4 : ℕ∞) := SimpleGraph.egirth_le_length hw
  have h94 : (9 : ℕ∞) ≤ (4 : ℕ∞) := le_trans hgirth hle
  revert h94
  norm_num
