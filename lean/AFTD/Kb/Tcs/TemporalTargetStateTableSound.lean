import AFTD.Prelude
import AFTD.Kb.Tcs.IsTemporalWalk

/-!
# temporal_target_state_table_sound

Topic: graphs   Node: 9c537556b451

Provenance: helper lemma. Finite invariant-table soundness lemma for certificates used in the OP-80 deep session, arXiv:2610.06228 Sec. 7.

If a finite table of endpoint/target-set pairs contains the initial state and is closed under every legal temporal step, then every temporal walk has a table state whose set contains all targets it has visited.
-/

theorem temporal_target_state_table_sound {n : ℕ} (G : ℕ → SimpleGraph (Fin n))
    (U : Finset (Fin n)) (s : Fin n) (T : ℕ)
    (S : ℕ → Finset (Fin n × Finset (Fin n))) (M0 : Finset (Fin n))
    (hinit : (s, M0) ∈ S 0) (hstart : s ∈ U → s ∈ M0)
    (hstep : ∀ t : Fin T, ∀ p ∈ S t.val, ∀ u : Fin n,
      u = p.1 ∨ (G t.val).Adj p.1 u →
      (u, if u ∈ U then insert u p.2 else p.2) ∈ S (t.val + 1))
    (w : ℕ → Fin n) (hw0 : w 0 = s) (hw : is_temporal_walk G w) :
    ∃ M : Finset (Fin n), (w T, M) ∈ S T ∧
      ∀ i ≤ T, w i ∈ U → w i ∈ M := by
  have hinv : ∀ t ≤ T, ∃ M : Finset (Fin n), (w t, M) ∈ S t ∧
      ∀ i ≤ t, w i ∈ U → w i ∈ M := by
    intro t
    induction t with
    | zero =>
      intro ht
      refine ⟨M0, by simpa [hw0] using hinit, ?_⟩
      intro i hi hui
      obtain rfl : i = 0 := by omega
      simpa [hw0] using hstart (by simpa [hw0] using hui)
    | succ t ih =>
      intro ht
      obtain ⟨M, hM, hcover⟩ := ih (by omega)
      let M' := if w (t + 1) ∈ U then insert (w (t + 1)) M else M
      refine ⟨M', hstep ⟨t, by omega⟩ (w t, M) hM (w (t + 1)) (hw t), ?_⟩
      intro i hi hui
      by_cases h : i ≤ t
      · have hm := hcover i h hui
        dsimp [M']
        split_ifs
        · exact Finset.mem_insert_of_mem hm
        · exact hm
      · obtain rfl : i = t + 1 := by omega
        simp [M', hui]
  exact hinv T le_rfl
