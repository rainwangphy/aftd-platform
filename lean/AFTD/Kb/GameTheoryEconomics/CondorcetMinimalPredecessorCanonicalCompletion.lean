import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalPredecessorCompletionIntegerCertificate

/-!
# condorcet_minimal_predecessor_canonical_completion

Topic: social_choice   Node: d4f2a685418a

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Constructive completion of the minimal-core incidence argument developed in this session; all four proofs were scratch-checked together in CanonicalAndTransport3.log. General supporting route lemmas, not a new election bound or a research novelty claim.

For a globally minimal S_k core, k positive, take a nonempty family of (k+1)-sets containing every set with no outside common predecessor. Adjoin one vertex per family member, put arrows from every core vertex to every new vertex, and from each new vertex to the members of its set. The resulting relation has S_(k+1), and the explicit integer incidence weights put every induced acyclic subset strictly below half the total.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_minimal_predecessor_canonical_completion
    (m k : ℕ) (hk : 0 < k) (R : Fin m → Fin m → Prop)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hminimal : ∀ S : Finset (Fin m),
      (∀ J : Finset (Fin m), J ⊆ S → J.card ≤ k →
        ∃ a ∈ S, a ∉ J ∧ ∀ b ∈ J, R a b) → S = univ)
    (F : Finset (Finset (Fin m))) (hF : F.Nonempty)
    (hcard : ∀ T ∈ F, T.card = k+1)
    (hcomplete : ∀ T : Finset (Fin m), T.card = k+1 →
      (¬∃ a, a ∉ T ∧ ∀ b ∈ T, R a b) → T ∈ F) :
    let Q := Fin m ⊕ {T : Finset (Fin m) // T ∈ F}
    let H : Q → Q → Prop := fun a b => match a,b with
      | .inl a,.inl b => R a b
      | .inl _,.inr _ => True
      | .inr T,.inl a => a ∈ T.val
      | .inr _,.inr _ => False
    let w : Q → ℕ := fun a => match a with
      | .inl a => F.card * (F.filter fun T => a∈T).card
      | .inr _ => (k+1)*F.card-1
    (∀ J : Finset Q, J.card ≤ k+1 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, H a b) ∧
    (∀ A : Finset Q,
      WellFounded (fun a b : {a : Q // a∈A} => H a.val b.val) →
      2*(∑ a∈A,w a) < ∑ a,w a) := by
  classical
  let Q := Fin m ⊕ {T : Finset (Fin m) // T ∈ F}
  let H : Q → Q → Prop := fun a b => match a,b with
    | .inl a,.inl b => R a b
    | .inl _,.inr _ => True
    | .inr T,.inl a => a ∈ T.val
    | .inr _,.inr _ => False
  let w : Q → ℕ := fun a => match a with
    | .inl a => F.card * (F.filter fun T => a∈T).card
    | .inr _ => (k+1)*F.card-1
  change (∀ J : Finset Q, J.card ≤ k+1 → ∃ a, a∉J ∧ ∀ b∈J,H a b) ∧
    (∀ A : Finset Q, WellFounded (fun a b : {a : Q // a∈A} => H a.val b.val) →
      2*(∑ a∈A,w a)<∑ a,w a)
  constructor
  · intro J hJ
    let A : Finset (Fin m) := univ.filter fun a => (Sum.inl a : Q)∈J
    have hAJ : A.map (Function.Embedding.inl) ⊆ J := by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      exact (mem_filter.mp ha).2
    have hAle : A.card ≤ k+1 := by
      have h := card_le_card hAJ
      simpa using h.trans hJ
    by_cases hAk : A.card ≤ k
    · obtain ⟨a,ha,har⟩ := hroot A hAk
      refine ⟨Sum.inl a,?_,?_⟩
      · exact fun h => ha (mem_filter.mpr ⟨mem_univ _,h⟩)
      · intro b hb
        cases b with
        | inl b => exact har b (mem_filter.mpr ⟨mem_univ _,hb⟩)
        | inr b => trivial
    · have hAc : A.card = k+1 := by omega
      have hEq : J = A.map Function.Embedding.inl := by
        symm
        apply eq_of_subset_of_card_le hAJ
        simpa [hAc] using hJ
      by_cases hAroot : ∃ a, a∉A ∧ ∀ b∈A,R a b
      · obtain ⟨a,ha,har⟩ := hAroot
        refine ⟨Sum.inl a,?_,?_⟩
        · exact fun h => ha (mem_filter.mpr ⟨mem_univ _,h⟩)
        · intro b hb
          rw [hEq] at hb
          obtain ⟨b,hbin,rfl⟩ := mem_map.mp hb
          exact har b hbin
      · let T : {T : Finset (Fin m) // T∈F} := ⟨A,hcomplete A hAc hAroot⟩
        refine ⟨Sum.inr T,?_,?_⟩
        · rw [hEq]
          simp [Function.Embedding.inl]
        · intro b hb
          rw [hEq] at hb
          obtain ⟨b,hbin,rfl⟩ := mem_map.mp hb
          exact hbin
  · intro X hX
    let A : Finset (Fin m) := univ.filter fun a => (Sum.inl a : Q)∈X
    let B : Finset {T : Finset (Fin m) // T∈F} :=
      univ.filter fun T => (Sum.inr T : Q)∈X
    let C : Finset (Finset (Fin m)) := B.image Subtype.val
    have hA : WellFounded (fun a b : {a : Fin m // a∈A} => R a.val b.val) := by
      let f : {a : Fin m // a∈A} → {a : Q // a∈X} :=
        fun a => ⟨Sum.inl a.val,(mem_filter.mp a.property).2⟩
      exact (InvImage.wf f hX).mono (fun _ _ h => h)
    have hCF : C ⊆ F := by
      intro T hT
      obtain ⟨T,_,rfl⟩ := mem_image.mp hT
      exact T.property
    have hCA : ∀ T∈C,Disjoint A T := by
      intro T hT
      obtain ⟨T,hTB,rfl⟩ := mem_image.mp hT
      apply disjoint_left.mpr
      intro a haA haT
      exact hX.asymmetric
        (a := ⟨Sum.inl a,(mem_filter.mp haA).2⟩)
        (b := ⟨Sum.inr T,(mem_filter.mp hTB).2⟩) (by trivial) haT
    have hbound := (condorcet_minimal_predecessor_completion_integer_certificate
      m k hk R hroot hminimal F hF hcard hcomplete).2 A C hA hCF hCA
    have hCcard : C.card = B.card := card_image_of_injective _ Subtype.val_injective
    have hsumX : (∑ x∈X,w x) =
        F.card*(∑ a∈A,(F.filter fun T => a∈T).card)+((k+1)*F.card-1)*C.card := by
      have hXu : (∑ x∈X,w x) = ∑ x : Q, if x∈X then w x else 0 := by
        simp
      rw [hXu,Fintype.sum_sum_type]
      change (∑ a : Fin m, if (Sum.inl a : Q)∈X then
          F.card*(F.filter fun T => a∈T).card else 0) +
        (∑ T : {T : Finset (Fin m) // T∈F}, if (Sum.inr T : Q)∈X then
          (k+1)*F.card-1 else 0) = _
      rw [← sum_filter,← sum_filter]
      change (∑ a∈A,F.card*(F.filter fun T => a∈T).card)+
        (∑ _T∈B,((k+1)*F.card-1)) = _
      rw [mul_sum, hCcard]
      simp [Nat.mul_comm]
    have hsum : (∑ x : Q,w x) =
        F.card*(∑ a : Fin m,(F.filter fun T => a∈T).card)+
          ((k+1)*F.card-1)*F.card := by
      rw [Fintype.sum_sum_type]
      simp [w,mul_sum,Nat.mul_comm]
    rw [hsumX,hsum]
    exact hbound
