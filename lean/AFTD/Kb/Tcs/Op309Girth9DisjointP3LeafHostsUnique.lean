import AFTD.Prelude
import AFTD.Kb.Tcs.Op309GirthNineNoFourCycle
import AFTD.Kb.Tcs.Op309GirthNineNoEightCycle

/-!
# op309_girth9_disjoint_p3_leaf_hosts_unique

Topic: graphs   Node: 2b075982b531

Provenance: helper lemma. High-girth shared-host obstruction for OP-309.

In a graph of girth at least nine, two vertex-disjoint three-vertex paths cannot both have leaves adjacent to each of two distinct outside vertices.
-/

private theorem in1254_no_six_cycle {V : Type*} (G : SimpleGraph V) (hgirth : (9 : ℕ∞) ≤ G.egirth)
    (a b c d e f : V) (hvertices : [a,b,c,d,e,f].Nodup)
    (hedges : G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e f ∧ G.Adj f a) : False := by
  rcases hedges with ⟨hab,hbc,hcd,hde,hef,hfa⟩
  let w : G.Walk a a := SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
    (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hde (SimpleGraph.Walk.cons hef
      (SimpleGraph.Walk.cons hfa SimpleGraph.Walk.nil)))))
  have hnotnil : ¬ w.Nil := by dsimp [w]; intro h; cases h
  have hw : w.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, by norm_num [w]⟩
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_tail_of_not_nil _ hnotnil]
    have hrot : [b,c,d,e,f,a] = [a,b,c,d,e,f].rotate 1 := by
      rw [List.rotate_cons_succ, List.rotate_zero]
      rfl
    change [b,c,d,e,f,a].Nodup
    rw [hrot]
    rwa [List.nodup_rotate]
  have hle : G.egirth ≤ (6 : ℕ∞) := G.egirth_le_length hw
  have hcontra : (9 : ℕ∞) ≤ (6 : ℕ∞) := hgirth.trans hle
  revert hcontra
  decide

theorem op309_girth9_disjoint_p3_leaf_hosts_unique
    {V : Type*} (G : SimpleGraph V) (hgirth : (9 : ℕ∞) ≤ G.egirth)
    (a b c d e f u v : V) (hvertices : [a,b,c,d,e,f,u,v].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hde : G.Adj d e) (hef : G.Adj e f)
    (huP : G.Adj u a ∨ G.Adj u c) (hvP : G.Adj v a ∨ G.Adj v c)
    (huQ : G.Adj u d ∨ G.Adj u f) (hvQ : G.Adj v d ∨ G.Adj v f) : False := by
  have hpairs := hvertices
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true,
    not_false_eq_true] at hpairs
  rcases huP with huP | huP <;> rcases hvP with hvP | hvP <;>
    rcases huQ with huQ | huQ <;> rcases hvQ with hvQ | hvQ
  · apply op309_girth_nine_no_four_cycle G hgirth u a v d
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hvP.symm, hvQ, huQ.symm⟩
  · apply in1254_no_six_cycle G hgirth u a v f e d
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hvP.symm, hvQ, hef.symm, hde.symm, huQ.symm⟩
  · apply in1254_no_six_cycle G hgirth u a v d e f
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hvP.symm, hvQ, hde, hef, huQ.symm⟩
  · apply op309_girth_nine_no_four_cycle G hgirth u a v f
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hvP.symm, hvQ, huQ.symm⟩
  · apply in1254_no_six_cycle G hgirth u a b c v d
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hab, hbc, hvP.symm, hvQ, huQ.symm⟩
  · apply op309_girth_nine_no_eight_cycle G hgirth u a b c v f e d
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hab, hbc, hvP.symm, hvQ, hef.symm, hde.symm, huQ.symm⟩
  · apply op309_girth_nine_no_eight_cycle G hgirth u a b c v d e f
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hab, hbc, hvP.symm, hvQ, hde, hef, huQ.symm⟩
  · apply in1254_no_six_cycle G hgirth u a b c v f
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hab, hbc, hvP.symm, hvQ, huQ.symm⟩
  · apply in1254_no_six_cycle G hgirth u c b a v d
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hbc.symm, hab.symm, hvP.symm, hvQ, huQ.symm⟩
  · apply op309_girth_nine_no_eight_cycle G hgirth u c b a v f e d
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hbc.symm, hab.symm, hvP.symm, hvQ, hef.symm, hde.symm, huQ.symm⟩
  · apply op309_girth_nine_no_eight_cycle G hgirth u c b a v d e f
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hbc.symm, hab.symm, hvP.symm, hvQ, hde, hef, huQ.symm⟩
  · apply in1254_no_six_cycle G hgirth u c b a v f
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hbc.symm, hab.symm, hvP.symm, hvQ, huQ.symm⟩
  · apply op309_girth_nine_no_four_cycle G hgirth u c v d
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hvP.symm, hvQ, huQ.symm⟩
  · apply in1254_no_six_cycle G hgirth u c v f e d
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hvP.symm, hvQ, hef.symm, hde.symm, huQ.symm⟩
  · apply in1254_no_six_cycle G hgirth u c v d e f
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hvP.symm, hvQ, hde, hef, huQ.symm⟩
  · apply op309_girth_nine_no_four_cycle G hgirth u c v f
    · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, and_true, not_false_eq_true]
      tauto
    · exact ⟨huP, hvP.symm, hvQ, huQ.symm⟩
