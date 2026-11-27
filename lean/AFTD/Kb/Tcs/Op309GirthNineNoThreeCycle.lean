import AFTD.Prelude

/-!
# op309_girth_nine_no_three_cycle

Topic: graphs   Node: 0f7b0588a51d

Provenance: helper lemma. OP-309 girth-nine canonical-port local cycle exclusions.

A graph of girth at least nine has no cycle of length 3 on distinct vertices.
-/

theorem op309_girth_nine_no_three_cycle
    {V : Type*} (G : SimpleGraph V) (hgirth : (9 : ℕ∞) ≤ G.egirth)
    (a b c : V) (hvertices : [a,b,c].Nodup)
    (hedges : G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) : False := by
  open SimpleGraph in
  rcases hedges with ⟨hab, hbc, hca⟩
  let p : G.Walk a a := Walk.cons hab (Walk.cons hbc (Walk.cons hca Walk.nil))
  have hlen : p.length = 3 := rfl
  have hnotnil : ¬ p.Nil := by simp [p]
  have hpath : p.tail.IsPath := by
    rw [Walk.isPath_def, Walk.support_tail_of_not_nil p hnotnil]
    change [b, c, a].Nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true] at hvertices ⊢
    tauto
  have hcycle : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    exact ⟨hpath, by rw [hlen]⟩
  have hle := G.egirth_le_length hcycle
  rw [hlen] at hle
  have : (9 : ℕ∞) ≤ 3 := hgirth.trans hle
  norm_num at this
