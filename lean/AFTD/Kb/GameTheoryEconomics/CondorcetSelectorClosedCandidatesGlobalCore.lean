import AFTD.Prelude
import AFTD.Kb.Tcs.G

/-!
# condorcet_selector_closed_candidates_global_core

Topic: social_choice   Node: 4ec5cd1aca1d

Provenance: helper lemma. IN-362 structural helper for the OP-19 acyclic-cover and optimized private-policy routes. Elementary finite image and closure argument. No new election bound or research advance.

Consider uniquely indexed three-candidate committees S(i), each with an outside root f(i), and the claim relation R(i,j) iff f(j) belongs to S(i). Suppose the only candidate set C of cardinal at least four that is closed under the selector (S(i) subset C implies f(i) in C) is the whole candidate set. Then the only induced claim subset retaining an outside common predecessor for every at-most-three claims is the whole claim graph. The proof extracts the candidate image f(B), proves it has at least four elements, and proves it is closed. Auxiliary lemmas also show that, when every triple is present, every closed candidate set with at least four members induces an S3 claim graph. Thus global core checks can be performed on candidate labels, without enumerating every claim subset.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_selector_core_lift_small_set
    {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]
    (S : I → Finset A) (f : I → A) (B : Finset I)
    (hB : ∀ J : Finset I, J ⊆ B → J.card ≤ 3 →
      ∃ i ∈ B, i ∉ J ∧ ∀ j ∈ J, f j ∈ S i)
    (T : Finset A) (hT : T ⊆ B.image f) (hcard : T.card ≤ 3) :
    ∃ i ∈ B, T ⊆ S i := by
  classical
  have hpre : ∀ a : T, ∃ i, i ∈ B ∧ f i = a.val := by
    intro a
    exact mem_image.mp (hT a.property)
  choose g hg using hpre
  let J : Finset I := T.attach.image g
  have hJB : J ⊆ B := by
    intro j hj
    obtain ⟨a,_,rfl⟩ := mem_image.mp hj
    exact (hg a).1
  have hJcard : J.card ≤ 3 := by
    exact (card_image_le.trans (by simpa using hcard))
  obtain ⟨i,hi,_,hdom⟩ := hB J hJB hJcard
  refine ⟨i,hi,?_⟩
  intro a ha
  have hd := hdom (g ⟨a,ha⟩) (mem_image.mpr ⟨⟨a,ha⟩,mem_attach _ _,rfl⟩)
  simpa only [(hg ⟨a,ha⟩).2] using hd

theorem condorcet_selector_core_root_image
    {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]
    (S : I → Finset A) (f : I → A)
    (hcard : ∀ i, (S i).card = 3) (hout : ∀ i, f i ∉ S i)
    (hinj : Function.Injective S) (B : Finset I)
    (hB : ∀ J : Finset I, J ⊆ B → J.card ≤ 3 →
      ∃ i ∈ B, i ∉ J ∧ ∀ j ∈ J, f j ∈ S i) :
    4 ≤ (B.image f).card ∧
    (∀ i, S i ⊆ B.image f → i ∈ B) ∧
    (∀ i, S i ⊆ B.image f → f i ∈ B.image f) := by
  classical
  have hsize : 4 ≤ (B.image f).card := by
    by_contra h
    have hsmall : (B.image f).card ≤ 3 := by omega
    obtain ⟨i,hi,hsub⟩ := condorcet_selector_core_lift_small_set S f B hB
      (B.image f) (Subset.refl _) hsmall
    exact hout i (hsub (mem_image.mpr ⟨i,hi,rfl⟩))
  have hmem : ∀ i, S i ⊆ B.image f → i ∈ B := by
    intro i hi
    obtain ⟨j,hj,hsub⟩ := condorcet_selector_core_lift_small_set S f B hB
      (S i) hi (by rw [hcard])
    have heq : S i = S j := eq_of_subset_of_card_le hsub (by rw [hcard,hcard])
    have hij : i = j := hinj heq
    simpa only [hij] using hj
  exact ⟨hsize,hmem,fun i hi => mem_image.mpr ⟨i,hmem i hi,rfl⟩⟩

theorem condorcet_selector_closed_candidates_predecessors
    {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]
    (S : I → Finset A) (f : I → A) (hout : ∀ i, f i ∉ S i)
    (hfull : ∀ T : Finset A, T.card = 3 → ∃ i, S i = T)
    (C : Finset A) (hC : 4 ≤ C.card)
    (hclosed : ∀ i, S i ⊆ C → f i ∈ C) :
    ∀ J : Finset I, J ⊆ univ.filter (fun i => S i ⊆ C) → J.card ≤ 3 →
      ∃ i ∈ univ.filter (fun i => S i ⊆ C), i ∉ J ∧ ∀ j ∈ J, f j ∈ S i := by
  classical
  intro J hJ hcard
  have himage : J.image f ⊆ C := by
    intro a ha
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
    exact hclosed j (mem_filter.mp (hJ hj)).2
  obtain ⟨T,hJT,hTC,hTcard⟩ := exists_subsuperset_card_eq himage
    (card_image_le.trans hcard) (show 3 ≤ C.card by omega)
  obtain ⟨i,hi⟩ := hfull T hTcard
  have hiC : S i ⊆ C := by simpa only [hi] using hTC
  refine ⟨i,mem_filter.mpr ⟨mem_univ _,hiC⟩,?_,?_⟩
  · intro hiJ
    apply hout i
    rw [hi]
    exact hJT (mem_image.mpr ⟨i,hiJ,rfl⟩)
  · intro j hj
    rw [hi]
    exact hJT (mem_image.mpr ⟨j,hj,rfl⟩)

theorem condorcet_selector_closed_candidates_global_core
    {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]
    (S : I → Finset A) (f : I → A)
    (hcard : ∀ i, (S i).card = 3) (hout : ∀ i, f i ∉ S i)
    (hinj : Function.Injective S)
    (hclosed : ∀ C : Finset A, 4 ≤ C.card →
      (∀ i, S i ⊆ C → f i ∈ C) → C = univ)
    (B : Finset I)
    (hB : ∀ J : Finset I, J ⊆ B → J.card ≤ 3 →
      ∃ i ∈ B, i ∉ J ∧ ∀ j ∈ J, f j ∈ S i) : B = univ := by
  classical
  obtain ⟨hsize,hmem,hclose⟩ := condorcet_selector_core_root_image S f hcard hout hinj B hB
  have hall := hclosed (B.image f) hsize hclose
  apply eq_univ_of_forall
  intro i
  apply hmem i
  rw [hall]
  exact subset_univ _
