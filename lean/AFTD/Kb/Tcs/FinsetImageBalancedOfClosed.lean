import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetIsMidpointBalanced

/-!
# finset_image_balanced_of_closed

Topic: combinatorics   Node: 285bd4798ccf

Provenance: helper lemma. step towards finset_midpoint_balanced_exists_nonzero_minor

If b is injective, u, v are midpoint witnesses with u i ≠ i, v i ≠ i, u i ≠ v i, and S is a nonempty subset closed under u and v, then b(S) is midpoint-balanced.
-/

/-- The image under an injective certificate map b of a non-empty subset S closed under u and v satisfying the midpoint identities and distinctness is midpoint-balanced. -/
theorem finset_image_balanced_of_closed {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {n : ℕ} (b : Fin n → G) (hinj : Function.Injective b)
    (u v : Fin n → Fin n)
    (hu : ∀ i, u i ≠ i) (hv : ∀ i, v i ≠ i) (huv : ∀ i, u i ≠ v i)
    (hmid : ∀ i, b i + b i = b (u i) + b (v i))
    (S : Finset (Fin n)) (hSne : S.Nonempty)
    (hS_closed : ∀ i ∈ S, u i ∈ S ∧ v i ∈ S) :
    finset_is_midpoint_balanced (S.image b) := by
  dsimp [finset_is_midpoint_balanced]
  constructor
  · exact Finset.Nonempty.image hSne b
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hui, hvi⟩ := hS_closed i hi
    refine ⟨b (u i), Finset.mem_image_of_mem b hui, b (v i), Finset.mem_image_of_mem b hvi, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hu i (hinj h)
    · intro h
      exact hv i (hinj h)
    · intro h
      exact huv i (hinj h)
    · exact hmid i
