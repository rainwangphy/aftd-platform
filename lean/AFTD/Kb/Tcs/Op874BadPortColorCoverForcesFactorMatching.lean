import AFTD.Prelude
import AFTD.Kb.Tcs.Op874BadMatchingPortsForceFactorMatching

/-!
# op874_bad_port_color_cover_forces_factor_matching

Topic: graphs   Node: 2a17a660cef2

Provenance: helper lemma. Structural two-port reduction for OP-874; experiments 43048, 43073 and 43075 test the local-state implications.

Suppose matching edges exchange two ownership classes, each vertex owns its matching edge or one of two symmetric distinct factor neighbors, and a factor edge whose color lies outside a distinguished high pair has an owner at one of its ends. If every matching-owner vertex meets such an edge, the owned factor edges form a perfect matching.
-/

theorem op874_bad_port_color_cover_forces_factor_matching {V : Type*} [Fintype V] [DecidableEq V]
    (flag : V → Bool) (mate own : V → V) (step : V → Fin 2 → V)
    (col : V → Fin 2 → Fin 6)
    (hmate : ∀ v, mate (mate v) = v)
    (hflip : ∀ v, flag (mate v) = !flag v)
    (howner : ∀ v, own v = mate v ∨ ∃ i, own v = step v i)
    (hflag : ∀ v, flag v = true ↔ own v = mate v)
    (hsym : ∀ v i, ∃ j, step (step v i) j = v)
    (hdist : ∀ v, step v 0 ≠ step v 1)
    (hnomatch : ∀ v i, step v i ≠ mate v)
    (hselected : ∀ v i, 4 ≤ (col v i).val →
      own v = step v i ∨ own (step v i) = v)
    (hbad : ∀ v, flag v = true → ∃ i, 4 ≤ (col v i).val) :
    ∀ v, ∃! i, own v = step v i ∨ own (step v i) = v := by
  classical
  have howneradj : ∀ q, flag q = false → ∃ i, step q i = own q := by
    intro q hq
    rcases howner q with hm | ⟨i, hi⟩
    · have ht := (hflag q).2 hm
      rw [hq] at ht
      contradiction
    · exact ⟨i, hi.symm⟩
  have hcover : ∀ p, flag p = true → ∃ q, flag q = false ∧ own q = p := by
    intro p hp
    obtain ⟨i, hi⟩ := hbad p hp
    have hpown := (hflag p).1 hp
    rcases hselected p i hi with hpedge | hqedge
    · exact False.elim ((hnomatch p i) (hpedge.symm.trans hpown))
    · let q := step p i
      have hqfalse : flag q = false := by
        cases hq : flag q with
        | false => rfl
        | true =>
          have heq := (hflag q).1 hq
          obtain ⟨j, hj⟩ := hsym p i
          have hne := hnomatch q j
          rw [show step q j = p from hj, ← heq, hqedge] at hne
          exact False.elim (hne rfl)
      exact ⟨q,hqfalse,hqedge⟩
  have hbase := op874_bad_matching_ports_force_factor_matching flag mate own step hmate hflip hcover howneradj hsym hdist
  intro v
  obtain ⟨i, hi, huniq⟩ := hbase v
  refine ⟨i, ?_, ?_⟩
  · rcases hi with ⟨_, h⟩ | ⟨_, h⟩ <;> simp_all
  · intro j hj
    apply huniq j
    rcases hj with hj | hj
    · have hf : flag v = false := by
        cases hv : flag v with
        | false => rfl
        | true =>
          have hm := (hflag v).1 hv
          exact False.elim ((hnomatch v j) (hj.symm.trans hm))
      exact Or.inl ⟨hf,hj⟩
    · have hf : flag (step v j) = false := by
        cases hv : flag (step v j) with
        | false => rfl
        | true =>
          have hm := (hflag (step v j)).1 hv
          obtain ⟨k, hk⟩ := hsym v j
          have hn := hnomatch (step v j) k
          rw [hk, ← hm, hj] at hn
          exact False.elim (hn rfl)
      exact Or.inr ⟨hf,hj⟩
