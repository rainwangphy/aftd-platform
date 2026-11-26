import AFTD.Prelude
import AFTD.Kb.Tcs.EqualExternalTripleForcesSharedExposedColor
import AFTD.Kb.Tcs.Op874SixCycleHookForcesMatchingPorts
import AFTD.Kb.Tcs.Op874SixCycleNextBlockForcesRepeat

/-!
# op874_six_cycle_five_interface_low_port_obstruction

Topic: graphs   Node: eacd023eeeeb

Provenance: helper lemma. Six-cycle open low-port kernel for OP-874; https://arxiv.org/abs/2610.41950.

On a six-cycle with bit word 011011 and a matching interface joining positions 1 and 5, the three indicated low-port selections already contradict compatibility on four cycle edges and that matching edge. All other interfaces, exact ownership and windows are irrelevant.
-/

private theorem core_high_ne_five (t : Fin 4) : Fin.castAdd 2 t ≠ (5 : Fin 6) := by
  fin_cases t <;> decide

private theorem core_high_inj {s t : Fin 4} (h : s ≠ t) :
    Fin.castAdd 2 s ≠ Fin.castAdd 2 t := by
  intro hh
  apply h
  apply Fin.ext
  simpa only [Fin.val_castAdd] using congrArg Fin.val hh


private theorem core_four_vec_inj (a b c d : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective ![a,b,c,d] := by
  intro i j he
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceEq] at he ⊢ <;> aesop

theorem op874_six_cycle_five_interface_low_port_obstruction :
    let b : Fin 6 → Bool := ![false,true,true,false,true,true]
    ¬ ∃ (w : Fin 6 → Fin 4) (h : Fin 6 → Fin 3 → Fin 6),
      (∀ i, w (i-1) ≠ w i) ∧
      (∀ i p q, p ≠ q → h i p ≠ h i q) ∧
      (∀ i p, h i p ≠ (if b i then 5 else 4) ∧
        h i p ≠ Fin.castAdd 2 (w (i-1)) ∧ h i p ≠ Fin.castAdd 2 (w i)) ∧
      (∀ i : Fin 6, (i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 5) →
        h i 0 ≠ h (i+1) 1 ∧ h i 0 ≠ h (i+1) 2 ∧
        h i 2 ≠ h (i+1) 1 ∧ h i 2 ≠ h (i+1) 2) ∧
      (h 1 0 ≠ h 5 0 ∧ h 1 0 ≠ h 5 1 ∧ h 1 1 ≠ h 5 0 ∧ h 1 1 ≠ h 5 1) ∧
      h 0 0 = 5 ∧ h 3 1 = 5 ∧ h 5 0 = 4 := by
  intro bit hex
  obtain ⟨w,h,hproper,hpair,havoid,hcycle,hmatch,hfix0,hfix3,hfix5⟩ := hex
  have hinj : ∀ i, Function.Injective (h i) := by
    intro i p q he
    by_contra hn
    exact hpair i p q hn he
  have hav : ∀ i p,
      h i p ≠ (if (![false,true,true,false,true,true] : Fin 6 → Bool) i then 5 else 4) ∧
      h i p ≠ Fin.castAdd 2 (w (i-1)) ∧ h i p ≠ Fin.castAdd 2 (w i) := by
    simpa [bit] using havoid
  have hc5 : h 5 0 ≠ h 0 1 ∧ h 5 0 ≠ h 0 2 ∧
      h 5 2 ≠ h 0 1 ∧ h 5 2 ≠ h 0 2 := by
    simpa using hcycle 5 (Or.inr (Or.inr (Or.inr rfl)))
  have hook := op874_six_cycle_hook_forces_matching_ports
    w h hproper hinj hav hc5 hmatch hfix0 hfix5
  have h04 : w 0 ≠ w 4 := by
    intro he
    apply (hav 5 2).2.1
    simpa [he] using hook.1
  have h05 : w 0 ≠ w 5 := by
    intro he
    apply (hav 5 2).2.2
    simpa [he] using hook.1
  have h14 : w 1 ≠ w 4 := by
    intro he
    apply (hav 5 1).2.1
    simpa [he] using hook.2.2
  have h15 : w 1 ≠ w 5 := by
    intro he
    apply (hav 5 1).2.2
    simpa [he] using hook.2.2
  have h01 : w 0 ≠ w 1 := by simpa using hproper 1
  have h45 : w 4 ≠ w 5 := by simpa using hproper 5
  have hfour : Function.Injective ![w 0,w 1,w 4,w 5] :=
    core_four_vec_inj (w 0) (w 1) (w 4) (w 5) h01 h04 h05 h14 h15 h45
  have hc3 : h 3 0 ≠ h 4 1 ∧ h 3 0 ≠ h 4 2 ∧
      h 3 2 ≠ h 4 1 ∧ h 3 2 ≠ h 4 2 := by
    simpa using hcycle 3 (Or.inr (Or.inl rfl))
  have hc4 : h 4 0 ≠ h 5 1 ∧ h 4 0 ≠ h 5 2 ∧
      h 4 2 ≠ h 5 1 ∧ h 4 2 ≠ h 5 2 := by
    simpa using hcycle 4 (Or.inr (Or.inr (Or.inl rfl)))
  have hnext : w 2 = w 0 := by
    apply op874_six_cycle_next_block_forces_repeat (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
      (h 3) (h 4) hfour
    · simpa using hproper 2
    · simpa using hproper 3
    · simpa using hproper 4
    · exact hinj 3
    · exact hinj 4
    · intro p; simpa using hav 3 p
    · intro p; simpa using hav 4 p
    · exact hfix3
    · exact hc3
    · exact ⟨by simpa [hook.1] using hc4.2.1,
        by simpa [hook.2.2] using hc4.1,
        by simpa [hook.1] using hc4.2.2.2,
        by simpa [hook.2.2] using hc4.2.2.1⟩
  have hx : h 1 0 ≠ 5 ∧ h 1 0 ≠ Fin.castAdd 2 (w 0) ∧
      h 1 0 ≠ Fin.castAdd 2 (w 1) := by simpa using hav 1 0
  have hy : h 1 2 ≠ 5 ∧ h 1 2 ≠ Fin.castAdd 2 (w 0) ∧
      h 1 2 ≠ Fin.castAdd 2 (w 1) := by simpa using hav 1 2
  have hu : h 2 1 ≠ 5 ∧ h 2 1 ≠ Fin.castAdd 2 (w 0) ∧
      h 2 1 ≠ Fin.castAdd 2 (w 1) := by
    have hh := hav 2 1
    simp only [hnext] at hh
    exact ⟨by simpa using hh.1, by simpa using hh.2.2, by simpa using hh.2.1⟩
  have hv : h 2 2 ≠ 5 ∧ h 2 2 ≠ Fin.castAdd 2 (w 0) ∧
      h 2 2 ≠ Fin.castAdd 2 (w 1) := by
    have hh := hav 2 2
    simp only [hnext] at hh
    exact ⟨by simpa using hh.1, by simpa using hh.2.2, by simpa using hh.2.1⟩
  have hxy : h 1 0 ≠ h 1 2 := hpair 1 0 2 (by decide)
  have huv : h 2 1 ≠ h 2 2 := hpair 2 1 2 (by decide)
  have hc1 : h 1 0 ≠ h 2 1 ∧ h 1 0 ≠ h 2 2 ∧
      h 1 2 ≠ h 2 1 ∧ h 1 2 ≠ h 2 2 := by
    simpa using hcycle 1 (Or.inl rfl)
  rcases equal_external_triple_forces_shared_exposed_color 5
      (Fin.castAdd 2 (w 0)) (Fin.castAdd 2 (w 1))
      (h 1 0) (h 1 2) (h 2 1) (h 2 2)
      (core_high_ne_five _).symm (core_high_ne_five _).symm (core_high_inj h01)
      hx hy hu hv hxy huv with he | he | he | he
  · exact hc1.1 he
  · exact hc1.2.1 he
  · exact hc1.2.2.1 he
  · exact hc1.2.2.2 he
