import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalPredecessorCompletionIntegerCertificate

/-!
# condorcet_minimal_predecessor_integer_reciprocal_separator

Topic: social_choice   Node: 7bc13de87995

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Constructive completion of the minimal-core incidence argument developed in this session; all four proofs were scratch-checked together in CanonicalAndTransport3.log. General supporting route lemmas, not a new election bound or a research novelty claim.

Given the same minimal core and uniform complete repair family, let the core map into any finite relation and choose a reciprocal common neighbor for each repair set. There are natural-number weights on the target, with explicit total Z*((k+1)*Z)+((k+1)*Z-1)*Z, strictly separating every induced acyclic subset below half. Neither the core map nor the chosen repair map needs to be injective.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_minimal_predecessor_integer_reciprocal_separator
    (m q k : ℕ) (hk : 0 < k)
    (R : Fin m → Fin m → Prop) (H : Fin q → Fin q → Prop)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hminimal : ∀ S : Finset (Fin m),
      (∀ J : Finset (Fin m), J ⊆ S → J.card ≤ k →
        ∃ a ∈ S, a ∉ J ∧ ∀ b ∈ J, R a b) → S = univ)
    (F : Finset (Finset (Fin m))) (hF : F.Nonempty)
    (hcard : ∀ T ∈ F, T.card = k+1)
    (hcomplete : ∀ T : Finset (Fin m), T.card = k+1 →
      (¬∃ a, a ∉ T ∧ ∀ b ∈ T, R a b) → T ∈ F)
    (f : Fin m → Fin q) (g : {T : Finset (Fin m) // T∈F} → Fin q)
    (hmap : ∀ a b, R a b → H (f a) (f b))
    (hrepair : ∀ T, ∀ a∈T.val, H (f a) (g T) ∧ H (g T) (f a)) :
    ∃ w : Fin q → ℕ,
      (∑ x,w x) = F.card*((k+1)*F.card)+((k+1)*F.card-1)*F.card ∧
      ∀ X : Finset (Fin q),
        WellFounded (fun a b : {a : Fin q // a∈X} => H a.val b.val) →
        2*(∑ x∈X,w x)<∑ x,w x := by
  classical
  let d : Fin m → ℕ := fun a => (F.filter fun T => a∈T).card
  let c := (k+1)*F.card-1
  let w : Fin q → ℕ := fun x =>
    (∑ a : Fin m,if f a=x then F.card*d a else 0)+
    (∑ T : {T : Finset (Fin m) // T∈F},if g T=x then c else 0)
  have hpush {α : Type} [Fintype α] (j : α → Fin q) (v : α → ℕ)
      (X : Finset (Fin q)) :
      (∑ x∈X, ∑ a,if j a=x then v a else 0) =
        ∑ a∈univ.filter (fun a => j a∈X),v a := by
    rw [sum_comm]
    simp [sum_filter]
  have hmass (X : Finset (Fin q)) :
      (∑ x∈X,w x) = F.card*(∑ a∈univ.filter (fun a => f a∈X),d a)+
        c*(univ.filter fun T => g T∈X).card := by
    dsimp only [w]
    rw [sum_add_distrib,hpush,hpush,← mul_sum]
    simp [Nat.mul_comm]
  have hcert := condorcet_minimal_predecessor_completion_integer_certificate
    m k hk R hroot hminimal F hF hcard hcomplete
  have hdegree : (∑ a,d a) = (k+1)*F.card := hcert.1
  have htotal : (∑ x,w x) = F.card*((k+1)*F.card)+c*F.card := by
    have h := hmass univ
    simpa only [mem_univ,filter_true,card_univ,Fintype.card_coe,hdegree] using h
  refine ⟨w,htotal,?_⟩
  intro X hX
  let A : Finset (Fin m) := univ.filter fun a => f a∈X
  let B : Finset {T : Finset (Fin m) // T∈F} := univ.filter fun T => g T∈X
  let C : Finset (Finset (Fin m)) := B.image Subtype.val
  have hA : WellFounded (fun a b : {a : Fin m // a∈A} => R a.val b.val) := by
    let j : {a : Fin m // a∈A} → {a : Fin q // a∈X} :=
      fun a => ⟨f a.val,(mem_filter.mp a.property).2⟩
    exact (InvImage.wf j hX).mono (fun a b hab => hmap a b hab)
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
      (a := ⟨f a,(mem_filter.mp haA).2⟩)
      (b := ⟨g T,(mem_filter.mp hTB).2⟩) (hrepair T a haT).1 (hrepair T a haT).2
  have hCcard : C.card = B.card := card_image_of_injective _ Subtype.val_injective
  have hbound := hcert.2 A C hA hCF hCA
  rw [hmass,htotal]
  simpa only [hCcard,hcert.1] using hbound
