import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetJoinCycleTensorMixedFiberBound
import AFTD.Kb.GameTheoryEconomics.CondorcetPrivateTripleStationarityObstruction

/-!
# condorcet_permutation_tensor_acyclic_lt_half

Topic: social_choice   Node: dd296bc694c9

Provenance: helper lemma. IN-372 supporting structural diagnostic for OP-19, 2026-10-30. Exact finite certificates and source/counting arguments documented in In372Oct30/ResearchNotes.txt. No novelty or research advance is claimed; the main election statement remains unchanged.

Let I be any nonempty finite type and choose one permutation of I for each of two sides. On vertices (side,index,t) with t in the fixed19-vertex residue tournament, put an arrow exactly when the tournament coordinate points forward and either the sides differ or the target index is the source-side permutation of the source index. Every induced acyclic vertex subset has cardinality strictly less than half of all38*card(I) vertices. Permutations may have arbitrary cycle structure and fixed points. This excludes this entire product family from supporting an acyclic half-cover; it does not give a universal S3 separator.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

theorem condorcet_wellFounded_no_permuted_cycle
    {V I : Type*} [Nonempty I] (R : V → V → Prop) (hR : WellFounded R)
    (e : Equiv.Perm I) (f : I → V) (hedge : ∀ i, R (f i) (f (e i))) : False := by
  classical
  obtain ⟨a,⟨j,hj⟩,hmin⟩ := hR.has_min (Set.range f) ⟨f (Classical.arbitrary I),
    ⟨Classical.arbitrary I,rfl⟩⟩
  apply hmin (f (e.symm j)) ⟨e.symm j,rfl⟩
  simpa only [e.apply_symm_apply, hj] using hedge (e.symm j)

theorem condorcet_wellFounded_no_three_cycle
    {V : Type*} (R : V → V → Prop) (hR : WellFounded R)
    (a b c : V) (hab : R a b) (hbc : R b c) (hca : R c a) : False := by
  apply condorcet_wellFounded_no_permuted_cycle R hR (finRotate 3) ![a,b,c]
  intro i
  fin_cases i
  · simpa [finRotate_apply] using hab
  · simpa [finRotate_apply] using hbc
  · simpa [finRotate_apply] using hca

theorem condorcet_wellFounded_no_four_cycle
    {V : Type*} (R : V → V → Prop) (hR : WellFounded R)
    (a b c d : V) (hab : R a b) (hbc : R b c) (hcd : R c d) (hda : R d a) : False := by
  apply condorcet_wellFounded_no_permuted_cycle R hR (finRotate 4) ![a,b,c,d]
  intro i
  fin_cases i
  · simpa [finRotate_apply] using hab
  · simpa [finRotate_apply] using hbc
  · simpa [finRotate_apply] using hcd
  · simpa [finRotate_apply] using hda

def condorcet_permutation_tensor_relation {I : Type*} (σ : Bool → Equiv.Perm I)
    (a b : Bool × I × Fin 19) : Prop :=
  (a.1 ≠ b.1 ∨ σ a.1 a.2.1 = b.2.1) ∧
    condorcet_private_stationary_relation a.2.2 b.2.2

def condorcet_permutation_tensor_fiber {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset (Bool × I × Fin 19)) (s : Bool) (t : Fin 19) : Finset I :=
  univ.filter fun i => (s,i,t) ∈ A

theorem condorcet_permutation_tensor_directed_triangle_bound
    {I : Type*} [Fintype I] [DecidableEq I] (σ : Bool → Equiv.Perm I)
    (A : Finset (Bool × I × Fin 19))
    (hA : WellFounded (fun a b : {a : Bool × I × Fin 19 // a ∈ A} =>
      condorcet_permutation_tensor_relation σ a.val b.val))
    (s : Bool) (t u v : Fin 19)
    (htu : condorcet_private_stationary_relation t u)
    (huv : condorcet_private_stationary_relation u v)
    (hvt : condorcet_private_stationary_relation v t)
    (hv : (condorcet_permutation_tensor_fiber A (!s) v).Nonempty) :
    (condorcet_permutation_tensor_fiber A s t).card +
      (condorcet_permutation_tensor_fiber A s u).card ≤ Fintype.card I := by
  classical
  obtain ⟨j,hj⟩ := hv
  have hdisj : Disjoint ((condorcet_permutation_tensor_fiber A s t).image (σ s))
      (condorcet_permutation_tensor_fiber A s u) := by
    apply disjoint_left.mpr
    intro k hk hk'
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
    let a : {a : Bool × I × Fin 19 // a ∈ A} := ⟨(s,i,t),(mem_filter.mp hi).2⟩
    let b : {a : Bool × I × Fin 19 // a ∈ A} := ⟨(s,σ s i,u),(mem_filter.mp hk').2⟩
    let c : {a : Bool × I × Fin 19 // a ∈ A} := ⟨(!s,j,v),(mem_filter.mp hj).2⟩
    apply condorcet_wellFounded_no_three_cycle _ hA a b c
    · exact ⟨Or.inr rfl,htu⟩
    · exact ⟨Or.inl (by change s ≠ !s; cases s <;> decide),huv⟩
    · exact ⟨Or.inl (by change (!s) ≠ s; cases s <;> decide),hvt⟩
  have h := card_le_univ (((condorcet_permutation_tensor_fiber A s t).image (σ s)) ∪
    condorcet_permutation_tensor_fiber A s u)
  rw [card_union_of_disjoint hdisj, card_image_of_injective _ (σ s).injective] at h
  exact h

theorem condorcet_permutation_tensor_triangle_bound
    {I : Type*} [Fintype I] [DecidableEq I] (σ : Bool → Equiv.Perm I)
    (A : Finset (Bool × I × Fin 19))
    (hA : WellFounded (fun a b : {a : Bool × I × Fin 19 // a ∈ A} =>
      condorcet_permutation_tensor_relation σ a.val b.val))
    (s : Bool) (t u v : Fin 19) (htri : condorcet_tensor_triangle t u v)
    (hv : (condorcet_permutation_tensor_fiber A (!s) v).Nonempty) :
    (condorcet_permutation_tensor_fiber A s t).card +
      (condorcet_permutation_tensor_fiber A s u).card ≤ Fintype.card I := by
  rcases htri with ⟨htu,huv,hvt⟩ | ⟨hut,htv,hvu⟩
  · exact condorcet_permutation_tensor_directed_triangle_bound σ A hA s t u v htu huv hvt hv
  · have h := condorcet_permutation_tensor_directed_triangle_bound σ A hA s u t v hut htv hvu hv
    omega

theorem condorcet_permutation_tensor_missing_fiber
    {I : Type*} [Fintype I] [DecidableEq I] (σ : Bool → Equiv.Perm I)
    (A : Finset (Bool × I × Fin 19))
    (hA : WellFounded (fun a b : {a : Bool × I × Fin 19 // a ∈ A} =>
      condorcet_permutation_tensor_relation σ a.val b.val)) :
    ∃ t, (condorcet_permutation_tensor_fiber A false t).card = 0 ∨
      (condorcet_permutation_tensor_fiber A true t).card = 0 := by
  classical
  by_contra h
  push_neg at h
  have hpos (s : Bool) (t : Fin 19) : (condorcet_permutation_tensor_fiber A s t).Nonempty := by
    apply card_pos.mp
    cases s <;> have hh := h t <;> omega
  obtain ⟨i0,hi0⟩ := hpos false 0
  obtain ⟨i1,hi1⟩ := hpos true 1
  obtain ⟨i2,hi2⟩ := hpos false 2
  obtain ⟨i3,hi3⟩ := hpos true 3
  let a : {a : Bool × I × Fin 19 // a ∈ A} := ⟨(false,i0,0),(mem_filter.mp hi0).2⟩
  let b : {a : Bool × I × Fin 19 // a ∈ A} := ⟨(true,i1,1),(mem_filter.mp hi1).2⟩
  let c : {a : Bool × I × Fin 19 // a ∈ A} := ⟨(false,i2,2),(mem_filter.mp hi2).2⟩
  let d : {a : Bool × I × Fin 19 // a ∈ A} := ⟨(true,i3,3),(mem_filter.mp hi3).2⟩
  apply condorcet_wellFounded_no_four_cycle _ hA a b c d
  · dsimp [a,b,c,d,condorcet_permutation_tensor_relation]
    exact ⟨Or.inl (by decide),by decide⟩
  · dsimp [a,b,c,d,condorcet_permutation_tensor_relation]
    exact ⟨Or.inl (by decide),by decide⟩
  · dsimp [a,b,c,d,condorcet_permutation_tensor_relation]
    exact ⟨Or.inl (by decide),by decide⟩
  · dsimp [a,b,c,d,condorcet_permutation_tensor_relation]
    exact ⟨Or.inl (by decide),by decide⟩

theorem condorcet_permutation_tensor_not_full_side
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (σ : Bool → Equiv.Perm I) (A : Finset (Bool × I × Fin 19))
    (hA : WellFounded (fun a b : {a : Bool × I × Fin 19 // a ∈ A} =>
      condorcet_permutation_tensor_relation σ a.val b.val)) (s : Bool) :
    ∃ i t, (s,i,t) ∉ A := by
  classical
  by_contra h
  push_neg at h
  let t : Fin 3 → Fin 19 := ![0,1,2]
  let f : I × Fin 3 → {a : Bool × I × Fin 19 // a ∈ A} :=
    fun p => ⟨(s,p.1,t p.2),h _ _⟩
  apply condorcet_wellFounded_no_permuted_cycle _ hA
    (Equiv.prodCongr (σ s) (finRotate 3)) f
  intro p
  refine ⟨Or.inr rfl,?_⟩
  change condorcet_private_stationary_relation (t p.2) (t (finRotate 3 p.2))
  have ht : ∀ j : Fin 3,
      condorcet_private_stationary_relation (t j) (t (finRotate 3 j)) := by decide
  exact ht p.2

theorem condorcet_permutation_tensor_card_fibers
    {I : Type*} [Fintype I] [DecidableEq I] (A : Finset (Bool × I × Fin 19)) :
    (∑ t, (condorcet_permutation_tensor_fiber A false t).card) +
      (∑ t, (condorcet_permutation_tensor_fiber A true t).card) = A.card := by
  classical
  have h : A.card = ∑ s : Bool, ∑ i : I, ∑ t : Fin 19,
      if (s,i,t) ∈ A then 1 else 0 := by
    calc
      A.card = ∑ p : Bool × I × Fin 19, if p ∈ A then 1 else 0 := by simp
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
  rw [h]
  simp only [condorcet_permutation_tensor_fiber, card_eq_sum_ones, sum_filter]
  rw [Fintype.sum_bool]
  rw [sum_comm (f := fun i : I => fun t : Fin 19 => if (false,i,t) ∈ A then 1 else 0)]
  rw [sum_comm (f := fun i : I => fun t : Fin 19 => if (true,i,t) ∈ A then 1 else 0)]
  omega

theorem condorcet_permutation_tensor_side_card
    {I : Type*} [Fintype I] [DecidableEq I] (s : Bool) :
    ((univ : Finset (Bool × I × Fin 19)).filter fun a => a.1 = s).card =
      19 * Fintype.card I := by
  simp only [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  cases s <;> simp [Nat.mul_comm]

theorem condorcet_permutation_tensor_acyclic_lt_half
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (σ : Bool → Equiv.Perm I) (A : Finset (Bool × I × Fin 19))
    (hA : WellFounded (fun a b : {a : Bool × I × Fin 19 // a ∈ A} =>
      condorcet_permutation_tensor_relation σ a.val b.val)) :
    2 * A.card < Fintype.card (Bool × I × Fin 19) := by
  classical
  let F := condorcet_permutation_tensor_fiber A
  have hsize : ∀ s t, (F s t).card ≤ Fintype.card I := fun s t => card_le_univ _
  have hk : 0 < Fintype.card I := Fintype.card_pos
  have hone (s : Bool) (hside : ∀ a ∈ A, a.1 = s) :
      2 * A.card < Fintype.card (Bool × I × Fin 19) := by
    let S := (univ : Finset (Bool × I × Fin 19)).filter fun a => a.1 = s
    have hsub : A ⊆ S := fun a ha => mem_filter.mpr ⟨mem_univ _,hside a ha⟩
    obtain ⟨i,t,hi⟩ := condorcet_permutation_tensor_not_full_side σ A hA s
    have hne : A ≠ S := by
      intro heq
      apply hi
      rw [heq]
      exact mem_filter.mpr ⟨mem_univ _,rfl⟩
    have hc := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hne⟩)
    rw [condorcet_permutation_tensor_side_card s] at hc
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    omega
  by_cases hlpos : ∃ t, 0 < (F false t).card
  · by_cases hrpos : ∃ t, 0 < (F true t).card
    · let l : Fin 19 → ℝ := fun t => (F false t).card
      let r : Fin 19 → ℝ := fun t => (F true t).card
      have hbound := condorcet_join_cycle_tensor_mixed_fiber_bound l r (Fintype.card I)
        (Nat.cast_nonneg _)
        (fun t => ⟨Nat.cast_nonneg _,by dsimp only [l,r]; exact_mod_cast hsize false t⟩)
        (fun t => ⟨Nat.cast_nonneg _,by dsimp only [l,r]; exact_mod_cast hsize true t⟩)
        (by obtain ⟨t,ht⟩ := hlpos; exact ⟨t,by dsimp only [l,r]; exact_mod_cast ht⟩)
        (by obtain ⟨t,ht⟩ := hrpos; exact ⟨t,by dsimp only [l,r]; exact_mod_cast ht⟩)
        (by
          obtain ⟨t,ht|ht⟩ := condorcet_permutation_tensor_missing_fiber σ A hA
          · exact ⟨t,Or.inl (by dsimp only [l,r,F]; exact_mod_cast ht)⟩
          · exact ⟨t,Or.inr (by dsimp only [l,r,F]; exact_mod_cast ht)⟩)
        (by
          intro a b c htri
          constructor
          · intro hc
            have hcN : 0 < (F true c).card := by dsimp only [l,r] at hc; exact_mod_cast hc
            have h := condorcet_permutation_tensor_triangle_bound σ A hA false a b c htri
              (card_pos.mp hcN)
            dsimp only [l,r,F]
            exact_mod_cast h
          · intro hc
            have hcN : 0 < (F false c).card := by dsimp only [l,r] at hc; exact_mod_cast hc
            have h := condorcet_permutation_tensor_triangle_bound σ A hA true a b c htri
              (card_pos.mp hcN)
            dsimp only [l,r,F]
            exact_mod_cast h)
      have hN : 2 * ((∑ t, (F false t).card)+(∑ t, (F true t).card)) ≤
          37 * Fintype.card I := by
        dsimp only [l,r] at hbound
        exact_mod_cast hbound
      rw [condorcet_permutation_tensor_card_fibers A] at hN
      simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
      omega
    · apply hone false
      intro a ha
      cases hs : a.1
      · rfl
      · have hmem : a.2.1 ∈ F true a.2.2 := by
          apply mem_filter.mpr
          refine ⟨mem_univ _,?_⟩
          simpa [← hs] using ha
        exact False.elim (hrpos ⟨a.2.2,card_pos.mpr ⟨a.2.1,hmem⟩⟩)
  · apply hone true
    intro a ha
    cases hs : a.1
    · have hmem : a.2.1 ∈ F false a.2.2 := by
        apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
        simpa [← hs] using ha
      exact False.elim (hlpos ⟨a.2.2,card_pos.mpr ⟨a.2.1,hmem⟩⟩)
    · rfl
