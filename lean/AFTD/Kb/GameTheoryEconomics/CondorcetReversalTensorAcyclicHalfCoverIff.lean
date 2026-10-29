import AFTD.Prelude
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.G

/-!
# condorcet_reversal_tensor_acyclic_half_cover_iff

Topic: social_choice   Node: 77f5e90159b4

Provenance: helper lemma. IN-357 structural diagnostic for the OP-19 acyclic-cover route, continuing IN-348 tensor experiment 8741. Categorical products and fractional acyclic colourings are standard, see https://www.ub.edu/comb/koljaknauer/Gil_manuscript.pdf , Sections 1.3 and 7.1. This is the ordinary homomorphism pullback argument; no novelty or research advance is asserted. It rules out a cover-cost improvement from tensoring a relation with its converse when a reversal map exists. Computation 8885 separately audits particular residue tournaments; their numeric maxima are not assumptions of this theorem.

Let R be any directed relation on Fin m, let n be any natural number, and suppose a map tau on Fin m reverses every R-arrow. The relation on pairs with an arrow from (a,b) to (c,d) exactly when R a c and R d b has an integer acyclic half-cover with n sets if and only if R has such a cover with the same n sets. A half-cover means each vertex belongs to at least half the sets, and every set induces a well-founded relation. No bijectivity of tau, positivity of n, or triple-predecessor property is assumed.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_tensor_half_cover_pullback
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (R : A → A → Prop) (T : B → B → Prop) (f : A → B)
    (hf : ∀ a b, R a b → T (f a) (f b)) (n : ℕ)
    (U : Fin n → Finset B)
    (hacyclic : ∀ v, WellFounded (fun a b : {a : B // a ∈ U v} => T a.val b.val)) :
    ∃ V : Fin n → Finset A,
      (∀ v, WellFounded (fun a b : {a : A // a ∈ V v} => R a.val b.val)) ∧
      (∀ a, (univ.filter fun v => a ∈ V v).card =
        (univ.filter fun v => f a ∈ U v).card) := by
  classical
  let V : Fin n → Finset A := fun v => univ.filter fun a => f a ∈ U v
  refine ⟨V, ?_, ?_⟩
  · intro v
    let g : {a : A // a ∈ V v} → {a : B // a ∈ U v} :=
      fun a => ⟨f a.val, (mem_filter.mp a.property).2⟩
    exact (InvImage.wf g (hacyclic v)).mono (fun a b hab => hf a.val b.val hab)
  · intro a
    congr 1
    ext v
    simp [V]

theorem condorcet_reversal_tensor_acyclic_half_cover_iff
    (m n : ℕ) (R : Fin m → Fin m → Prop)
    (τ : Fin m → Fin m) (hτ : ∀ a b, R a b → R (τ b) (τ a)) :
    (∃ U : Fin n → Finset (Fin m × Fin m),
      (∀ v, WellFounded (fun a b : {a : Fin m × Fin m // a ∈ U v} =>
        R a.val.1 b.val.1 ∧ R b.val.2 a.val.2)) ∧
      (∀ a, n ≤ 2 * (univ.filter fun v => a ∈ U v).card)) ↔
    (∃ V : Fin n → Finset (Fin m),
      (∀ v, WellFounded (fun a b : {a : Fin m // a ∈ V v} => R a.val b.val)) ∧
      (∀ a, n ≤ 2 * (univ.filter fun v => a ∈ V v).card)) := by
  classical
  constructor
  · rintro ⟨U, hU, hhalf⟩
    obtain ⟨V, hV, hcount⟩ := condorcet_tensor_half_cover_pullback R
      (fun a b : Fin m × Fin m => R a.1 b.1 ∧ R b.2 a.2)
      (fun a => (a, τ a)) (fun a b hab => ⟨hab, hτ a b hab⟩) n U hU
    refine ⟨V, hV, ?_⟩
    intro a
    rw [hcount a]
    exact hhalf (a, τ a)
  · rintro ⟨V, hV, hhalf⟩
    obtain ⟨U, hU, hcount⟩ := condorcet_tensor_half_cover_pullback
      (fun a b : Fin m × Fin m => R a.1 b.1 ∧ R b.2 a.2) R
      Prod.fst (fun a b hab => hab.1) n V hV
    refine ⟨U, hU, ?_⟩
    intro a
    rw [hcount a]
    exact hhalf a.1
