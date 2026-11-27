import AFTD.Prelude
import AFTD.Kb.Tcs.CycleMatchingLowColor

/-!
# op874_unused_low_color_has_unique_hidden_port

Topic: graphs   Node: 57b83fcd2265

Provenance: helper lemma. OP-874: local six-color ownership counting.

For one low external color, two distinct high external colors, and three distinct hidden colors disjoint from the external triple, exactly one hidden port uses the other low color.
-/

theorem op874_unused_low_color_has_unique_hidden_port
    (b : Bool) (a d : Fin 6) (h : Fin 3 → Fin 6)
    (ha : 2 ≤ a.val) (hd : 2 ≤ d.val) (had : a ≠ d)
    (hinj : Function.Injective h)
    (havoid : ∀ p, h p ≠ cycle_matching_low_color b ∧ h p ≠ a ∧ h p ≠ d) :
    ∃! p, h p = cycle_matching_low_color (!b) := by
  classical
  have hla : cycle_matching_low_color b ≠ a := by
    intro he
    have hv := congrArg Fin.val he
    cases b <;> simp [cycle_matching_low_color] at hv <;> omega
  have hld : cycle_matching_low_color b ≠ d := by
    intro he
    have hv := congrArg Fin.val he
    cases b <;> simp [cycle_matching_low_color] at hv <;> omega
  let A : Finset (Fin 6) := {cycle_matching_low_color b,a,d}
  let H : Finset (Fin 6) := Finset.univ.image h
  have hAc : A.card=3 := by simp [A,hla,hld,had]
  have hHc : H.card=3 := by simp [H,Finset.card_image_of_injective _ hinj]
  have hdis : Disjoint A H := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxH
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hxH
    have ha' := havoid p
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at hxA
    rcases hxA with hh | hh | hh
    · exact ha'.1 hh
    · exact ha'.2.1 hh
    · exact ha'.2.2 hh
  have hfull : A ∪ H = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdis,hAc,hHc]
    decide
  have hother : cycle_matching_low_color (!b) ∉ A := by
    simp only [A,Finset.mem_insert,Finset.mem_singleton,not_or]
    refine ⟨?_,?_,?_⟩
    · cases b <;> decide
    · intro hh
      have hv := congrArg Fin.val hh
      cases b <;> simp [cycle_matching_low_color] at hv <;> omega
    · intro hh
      have hv := congrArg Fin.val hh
      cases b <;> simp [cycle_matching_low_color] at hv <;> omega
  have hmem : cycle_matching_low_color (!b) ∈ H := by
    have hh : cycle_matching_low_color (!b) ∈ A ∪ H := by rw [hfull]; exact Finset.mem_univ _
    exact (Finset.mem_union.mp hh).resolve_left hother
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hmem
  exact ⟨p,hp,fun q hq => hinj (hq.trans hp.symm)⟩
