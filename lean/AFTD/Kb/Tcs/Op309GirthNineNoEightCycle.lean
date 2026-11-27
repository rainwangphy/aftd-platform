import AFTD.Prelude

/-!
# op309_girth_nine_no_eight_cycle

Topic: graphs   Node: 709867e510bb

Provenance: helper lemma. OP-309 girth-nine canonical-port local cycle exclusions.

A graph of girth at least nine has no cycle of length 8 on distinct vertices.
-/

theorem op309_girth_nine_no_eight_cycle
    {V : Type*} (G : SimpleGraph V) (hgirth : (9 : ℕ∞) ≤ G.egirth)
    (a b c d e f g h : V) (hvertices : [a,b,c,d,e,f,g,h].Nodup)
    (hedges : G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e f ∧ G.Adj f g ∧ G.Adj g h ∧ G.Adj h a) : False := by
  rcases hedges with ⟨hab, hbc, hcd, hde, hef, hfg, hgh, hha⟩
  let p : G.Walk a a :=
    SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hde
      (SimpleGraph.Walk.cons hef (SimpleGraph.Walk.cons hfg (SimpleGraph.Walk.cons hgh (SimpleGraph.Walk.cons hha SimpleGraph.Walk.nil)))))))
  have hnotnil : ¬ p.Nil := by
    dsimp [p]
    intro hc
    cases hc
  have hcycle : p.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_tail_of_not_nil _ hnotnil]
      have hrot : [b, c, d, e, f, g, h, a] = [a, b, c, d, e, f, g, h].rotate 1 := by
        rw [List.rotate_cons_succ, List.rotate_zero]
        rfl
      change [b, c, d, e, f, g, h, a].Nodup
      rw [hrot]
      rwa [List.nodup_rotate]
    · change 3 ≤ 8
      decide
  have hle : G.egirth ≤ ↑p.length := G.egirth_le_length hcycle
  have hlen : p.length = 8 := rfl
  rw [hlen] at hle
  have hcontra : (9 : ℕ∞) ≤ 8 := hgirth.trans hle
  revert hcontra
  decide
