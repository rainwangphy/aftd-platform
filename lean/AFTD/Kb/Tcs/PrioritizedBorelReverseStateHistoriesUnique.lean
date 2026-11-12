import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.TreeGameEdge

/-!
# prioritized_borel_reverse_state_histories_unique

Topic: automata   Node: 308a52429fe9

Provenance: helper lemma. Structural step related to arXiv:2611.10136, Conjecture 19.

If a tree-game edge is reverse-deterministic in the state at each fixed parent node and child direction, then at most one state history reaches any fixed node and final state.
-/

open Set
set_option maxHeartbeats 1000000

def op1385StateHistories {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (v : List Bool) (q : Q) : Set (Fin (v.length + 1) → Q) :=
  {h | h 0 = G.init_state ∧ h (Fin.last v.length) = q ∧
    ∀ i : Fin v.length, ∃ e ∈ G.edges, e.source_node = v.take i.val ∧
      e.source_state = h i.castSucc ∧ e.dir = v.get i ∧ e.target_state = h i.succ}

theorem prioritized_borel_reverse_state_histories_unique {Q : Type} {k : ℕ}
    (G : PrioritizedBorelGame Q k)
    (hback : ∀ e ∈ G.edges, ∀ e' ∈ G.edges,
      e.source_node = e'.source_node → e.dir = e'.dir →
      e.target_state = e'.target_state → e.source_state = e'.source_state)
    (v : List Bool) (q : Q) : (op1385StateHistories G v q).Subsingleton := by
  intro h hh h' hh'
  have hrev : ∀ j : ℕ, ∀ hj : j ≤ v.length,
      h ⟨v.length - j, by omega⟩ = h' ⟨v.length - j, by omega⟩ := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hz : (⟨v.length - 0, by omega⟩ : Fin (v.length + 1)) = Fin.last v.length := by
        apply Fin.ext
        simp
      simpa only [hz] using hh.2.1.trans hh'.2.1.symm
    | succ j ih =>
      intro hj
      let i : Fin v.length := ⟨v.length - (j + 1), by omega⟩
      obtain ⟨e, he, hen, hes, hed, het⟩ := hh.2.2 i
      obtain ⟨e', he', hen', hes', hed', het'⟩ := hh'.2.2 i
      have ht : e.target_state = e'.target_state := by
        rw [het, het']
        have hprev := ih (by omega)
        convert hprev using 1 <;> congr 1 <;> apply Fin.ext <;> simp [i] <;> omega
      have hs := hback e he e' he' (hen.trans hen'.symm) (hed.trans hed'.symm) ht
      rw [hes, hes'] at hs
      exact hs
  funext i
  have h := hrev (v.length - i.val) (by omega)
  convert h using 1 <;> congr 1 <;> apply Fin.ext <;> simp <;> omega
