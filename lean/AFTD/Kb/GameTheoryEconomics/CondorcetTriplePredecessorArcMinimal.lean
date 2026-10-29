import AFTD.Prelude

/-!
# condorcet_triple_predecessor_arc_minimal

Topic: social_choice   Node: cb0f7a8c3e5c

Provenance: helper lemma. IN-362 structural helper for OP-19 and condorcet_dimension_le_three_iff_acyclic_weight_separation. Elementary finite arc minimization, no new election bound or research advance.

Every finite relation in which each set of at most three vertices has an outside common predecessor has an irreflexive subrelation retaining that property such that every retained arrow a to b belongs to a private triple at a: there is a set J of exactly three vertices, containing b and excluding a, for which a is the unique outside common predecessor. No bound on the vertex count is asserted.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_triple_predecessor_arc_minimal (m : ℕ) (R : Fin m → Fin m → Prop)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) :
    ∃ Q : Fin m → Fin m → Prop,
      (∀ a b, Q a b → R a b) ∧ (∀ a, ¬ Q a a) ∧
      (∀ J : Finset (Fin m), J.card ≤ 3 →
        ∃ a, a ∉ J ∧ ∀ b ∈ J, Q a b) ∧
      (∀ a b, Q a b → ∃ J : Finset (Fin m), J.card = 3 ∧ b ∈ J ∧ a ∉ J ∧
        (∀ c ∈ J, Q a c) ∧
        ∀ d, d ∉ J → (∀ c ∈ J, Q d c) → d = a) := by
  classical
  let E : Finset (Fin m × Fin m) := univ.filter (fun e => R e.1 e.2 ∧ e.1 ≠ e.2)
  let P : Finset (Fin m × Fin m) → Prop := fun F =>
    ∀ J : Finset (Fin m), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, (a,b) ∈ F
  let family := E.powerset.filter P
  have hE : P E := by
    intro J hJ
    obtain ⟨a, ha, hR⟩ := hroot J hJ
    refine ⟨a, ha, fun b hb => mem_filter.mpr ⟨mem_univ _, hR b hb, ?_⟩⟩
    intro hab
    have hab' : a = b := hab
    exact ha (hab'.symm ▸ hb)
  have hEF : E ∈ family := mem_filter.mpr ⟨mem_powerset.mpr (subset_refl E), hE⟩
  obtain ⟨F,hF,hmin⟩ := family.exists_min_image Finset.card ⟨E,hEF⟩
  have hsub : F ⊆ E := mem_powerset.mp (mem_filter.mp hF).1
  have hP : P F := (mem_filter.mp hF).2
  let Q := fun a b => (a,b) ∈ F
  refine ⟨Q, ?_, ?_, hP, ?_⟩
  · intro a b hab
    exact (mem_filter.mp (hsub hab)).2.1
  · intro a haa
    exact (mem_filter.mp (hsub haa)).2.2 rfl
  · intro a b hab
    have hbad : ¬ P (F.erase (a,b)) := by
      intro h
      have hmem : F.erase (a,b) ∈ family :=
        mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset _ _).trans hsub), h⟩
      have hle := hmin _ hmem
      have hlt := card_erase_lt_of_mem hab
      omega
    have hex : ∃ J : Finset (Fin m), J.card ≤ 3 ∧
        ¬ ∃ d, d ∉ J ∧ ∀ c ∈ J, (d,c) ∈ F.erase (a,b) := by
      by_contra h
      apply hbad
      intro J hJ
      by_contra hno
      exact h ⟨J,hJ,hno⟩
    obtain ⟨J,hJ,hno⟩ := hex
    obtain ⟨d,hd,hdQ⟩ := hP J hJ
    have hprivate : ∀ d, d ∉ J → (∀ c ∈ J, Q d c) → d = a := by
      intro d hd hdQ
      by_contra hda
      apply hno
      refine ⟨d, hd, fun c hc => mem_erase.mpr ⟨?_, hdQ c hc⟩⟩
      intro heq
      exact hda (congrArg Prod.fst heq)
    have hda : d = a := hprivate d hd hdQ
    subst d
    have hbJ : b ∈ J := by
      by_contra hb
      apply hno
      refine ⟨a,hd,fun c hc => mem_erase.mpr ⟨?_,hdQ c hc⟩⟩
      intro heq
      have hcb : c = b := congrArg Prod.snd heq
      exact hb (hcb ▸ hc)
    have hthree : J.card = 3 := by
      by_contra hn
      have hcard : (insert a J).card ≤ 3 := by
        rw [card_insert_of_notMem hd]
        omega
      obtain ⟨r,hr,hrQ⟩ := hP (insert a J) hcard
      have hra : r = a := hprivate r
        (fun h => hr (mem_insert_of_mem h))
        (fun c hc => hrQ c (mem_insert_of_mem hc))
      subst r
      exact hr (mem_insert_self _ _)
    exact ⟨J,hthree,hbJ,hd,hdQ,hprivate⟩
