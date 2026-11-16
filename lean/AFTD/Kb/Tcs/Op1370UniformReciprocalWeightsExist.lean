import AFTD.Prelude

/-!
# op1370_uniform_reciprocal_weights_exist

Topic: combinatorics   Node: b27c5362684e

Provenance: helper lemma.

An uncomplemented family admits reciprocal weights that are uniform on the family.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_uniform_reciprocal_weights_exist
    {α V K : Type*} [Fintype α] [DecidableEq α] [Fintype V] [Field K]
    (A : V → Finset α) (hunc : ∀ x y, (A x)ᶜ ≠ A y) (u : K) (hu : u ≠ 0) :
    ∃ q : Finset α → K, (∀ X, q X * q Xᶜ = 1) ∧ ∀ x, q (A x) = u := by
  classical
  let F : Finset (Finset α) := Finset.univ.image A
  have hdis : ∀ X, X ∈ F → Xᶜ ∉ F := by
    intro X hX hXc
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hX
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hXc
    subst X
    exact hunc a b hb.symm
  let q : Finset α → K := fun X => if X ∈ F then u else if Xᶜ ∈ F then u⁻¹ else 1
  refine ⟨q, ?_, ?_⟩
  · intro X
    by_cases hX : X ∈ F
    · have hXc : Xᶜ ∉ F := hdis X hX
      simp [q, hX, hXc, hu]
    · by_cases hXc : Xᶜ ∈ F
      · simp [q, hX, hXc, hu]
      · simp [q, hX, hXc]
  · intro x
    have hx : A x ∈ F := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    simp [q, hx]
