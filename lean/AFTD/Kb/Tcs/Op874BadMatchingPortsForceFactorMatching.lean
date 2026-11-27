import AFTD.Prelude
import AFTD.Kb.Tcs.Op874OppositePairedCoverIsBijective

/-!
# op874_bad_matching_ports_force_factor_matching

Topic: graphs   Node: 85819f1fc7b8

Provenance: helper lemma. Structural reduction for the exact-owner global-pair route to OP-874; experiment 43048 tests the hypotheses.

In a finite set with two distinct symmetric factor neighbors per vertex, a class-switching matching involution, and an ownership map, suppose every false vertex owns a factor neighbor and every true vertex is owned by a false vertex. Then the undirected factor edges owned at one endpoint form a perfect matching.
-/

theorem op874_bad_matching_ports_force_factor_matching {V : Type*} [Fintype V] [DecidableEq V]
    (flag : V → Bool) (mate own : V → V) (step : V → Fin 2 → V)
    (hmate : ∀ v, mate (mate v) = v)
    (hflip : ∀ v, flag (mate v) = !flag v)
    (hcover : ∀ p, flag p = true → ∃ q, flag q = false ∧ own q = p)
    (howneradj : ∀ q, flag q = false → ∃ i, step q i = own q)
    (hsym : ∀ v i, ∃ j, step (step v i) j = v)
    (hdist : ∀ v, step v 0 ≠ step v 1) :
    ∀ v, ∃! i, (flag v = false ∧ own v = step v i) ∨
      (flag (step v i) = false ∧ own (step v i) = v) := by
  classical
  have hb := op874_opposite_paired_cover_is_bijective flag mate own hmate hflip hcover
  intro v
  have hinjstep : Function.Injective (step v) := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hdist v h)
    · exact False.elim (hdist v h.symm)
    · rfl
  cases hv : flag v with
  | false =>
    obtain ⟨i, hi⟩ := howneradj v hv
    refine ⟨i, Or.inl ⟨rfl, hi.symm⟩, ?_⟩
    intro j hj
    have hstep : step v j = own v := by
      rcases hj with ⟨_, h⟩ | ⟨hf, ho⟩
      · exact h.symm
      · have ht := (hb (step v j) hf).1
        rw [ho, hv] at ht
        contradiction
    have heq : step v j = step v i := hstep.trans hi.symm
    exact hinjstep heq
  | true =>
    obtain ⟨q, hq, hqown⟩ := hcover v hv
    obtain ⟨i, hi⟩ := howneradj q hq
    have hi' : step q i = v := hi.trans hqown
    obtain ⟨j, hj⟩ := hsym q i
    rw [hi'] at hj
    refine ⟨j, Or.inr ⟨hj ▸ hq, by rw [hj]; exact hqown⟩, ?_⟩
    intro k hk
    have hkq : step v k = q := by
      rcases hk with ⟨hf, _⟩ | ⟨hf, ho⟩
      · contradiction
      · symm
        apply (hb (step v k) hf).2 q hq
        exact hqown.trans ho.symm
    have heq : step v k = step v j := hkq.trans hj.symm
    exact hinjstep heq
