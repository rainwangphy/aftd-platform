import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385BlockMoves
import AFTD.Kb.Tcs.TreeGameEdge

/-!
# prioritized_borel_encoding_actions_eq_block

Topic: automata   Node: 64a566f942a0

Provenance: helper lemma. Controlled block simulation for arXiv:2611.10136, Conjecture 19.

A sequence of zero-priority actions followed by a final action with the original priority equals the encoded edge-action block when its bits form the edge's full code.
-/

lemma enc1385LocalActionsEqBlock {Q : Type} [Fintype Q] (e : TreeGameEdge Q 3)
    (xs : List (Bool × Fin 3)) (bit : Bool)
    (hzero : ∀ a ∈ xs, a.2 = 0)
    (hbits : xs.map Prod.fst ++ [bit] = enc1385Block e) :
    xs ++ [(bit,e.prio)] = enc1385BlockMoves e := by
  classical
  have hlen : xs.length = Fintype.card Q := by
    have h := congrArg List.length hbits
    simp [enc1385Block, enc1385StateCode] at h
    omega
  apply List.ext_getElem
  · simp [enc1385BlockMoves, hlen]
  · intro i hiL hiR
    by_cases hi : i < xs.length
    · have hz : xs[i].2 = 0 := hzero _ (List.getElem_mem hi)
      have hb : (enc1385Block e).getD i false = xs[i].1 := by
        rw [← hbits, List.getD_append _ _ _ _ (by simpa using hi)]
        simp [List.getD_eq_getElem, hi]
      have hne : i ≠ Fintype.card Q := by omega
      simp [enc1385BlockMoves, List.getElem_append_left hi, hne]
      apply Prod.ext
      · simpa only [List.getD_eq_getElem?_getD] using hb.symm
      · exact hz
    · have hieq : i = xs.length := by
        simp only [List.length_append, List.length_singleton] at hiL
        omega
      subst i
      have hb : (enc1385Block e).getD xs.length false = bit := by
        rw [← hbits, List.getD_append_right _ _ _ _ (by simp)]
        simp
      simp [enc1385BlockMoves, hlen]
      simpa only [hlen, List.getD_eq_getElem?_getD] using hb.symm

theorem prioritized_borel_encoding_actions_eq_block {Q : Type} [Fintype Q] (e : TreeGameEdge Q 3) (xs : List (Bool × Fin 3)) (bit : Bool) (hzero : ∀ a ∈ xs, a.2 = 0) (hbits : xs.map Prod.fst ++ [bit] = enc1385Block e) : xs ++ [(bit,e.prio)] = enc1385BlockMoves e := by
  exact enc1385LocalActionsEqBlock e xs bit hzero hbits
