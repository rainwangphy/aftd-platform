import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalPredecessorIntegerReciprocalSeparator
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalPredecessorUndominatedExtension

/-!
# condorcet_minimal_predecessor_reciprocal_completion_integer_weights

Topic: social_choice   Node: fc1a3c8992ad

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Constructive completion of the minimal-core incidence argument developed in this session; all four proofs were scratch-checked together in CanonicalAndTransport3.log. General supporting route lemmas, not a new election bound or a research novelty claim.

If a globally minimal finite S_k core with k positive maps into a finite relation, preserving arrows, and every missing (k+1)-set has a common reciprocal neighbor there, then natural-number vertex weights put every induced acyclic subset strictly below half the total. This strengthens the earlier real-weight existence result to a direct integer construction for the same structural family; arbitrary one-way repairs remain outside its hypotheses.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_minimal_predecessor_reciprocal_completion_integer_weights
    (m q k : ℕ) (hk : 0 < k)
    (R : Fin m → Fin m → Prop) (H : Fin q → Fin q → Prop) (f : Fin m → Fin q)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hminimal : ∀ S : Finset (Fin m),
      (∀ J : Finset (Fin m), J ⊆ S → J.card ≤ k →
        ∃ a ∈ S, a ∉ J ∧ ∀ b ∈ J, R a b) → S = univ)
    (hmap : ∀ a b, R a b → H (f a) (f b))
    (hrepair : ∀ T : Finset (Fin m), T.card = k+1 →
      (¬∃ a, a ∉ T ∧ ∀ b ∈ T, R a b) →
      ∃ x : Fin q, ∀ a ∈ T, H x (f a) ∧ H (f a) x) :
    ∃ w : Fin q → ℕ, ∀ A : Finset (Fin q),
      WellFounded (fun a b : {a : Fin q // a∈A} => H a.val b.val) →
      2*(∑ a∈A,w a) < ∑ a,w a := by
  classical
  let F : Finset (Finset (Fin m)) := univ.filter fun T =>
    T.card = k+1 ∧ ¬∃ a,a∉T ∧ ∀ b∈T,R a b
  have hF : F.Nonempty := by
    obtain ⟨T,hTc,hTb⟩ := condorcet_minimal_predecessor_undominated_extension
      m k R hroot hminimal
    exact ⟨T,mem_filter.mpr ⟨mem_univ _,hTc,hTb⟩⟩
  have hcard : ∀ T∈F,T.card=k+1 := fun T hT => (mem_filter.mp hT).2.1
  have hcomplete : ∀ T : Finset (Fin m), T.card=k+1 →
      (¬∃ a,a∉T ∧ ∀ b∈T,R a b) → T∈F :=
    fun T hc hb => mem_filter.mpr ⟨mem_univ _,hc,hb⟩
  have hex : ∀ T : {T : Finset (Fin m) // T∈F},
      ∃ x : Fin q, ∀ a∈T.val,H x (f a) ∧ H (f a) x := by
    intro T
    exact hrepair T.val (mem_filter.mp T.property).2.1 (mem_filter.mp T.property).2.2
  choose g hg using hex
  obtain ⟨w,_,hw⟩ := condorcet_minimal_predecessor_integer_reciprocal_separator
    m q k hk R H hroot hminimal F hF hcard hcomplete f g hmap
    (fun T a ha => ⟨(hg T a ha).2,(hg T a ha).1⟩)
  exact ⟨w,hw⟩
