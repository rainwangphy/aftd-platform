import AFTD.Prelude

/-!
# card_filter_subset_le_one_of_card_eq

Topic: combinatorics   Node: 0b0ca2644872

Provenance: helper lemma. arXiv:2610.37315 Theorem 1.1

Let α be a type with decidable equality, let k be a natural number, and let ℱ be a finite family of finite subsets of α such that every F ∈ ℱ has cardinality k. For any finite subset A of α with cardinality k, the number of sets in ℱ containing A is at most 1.
-/

/-- In a k-uniform family of sets, at most one member can contain a given set of size k. -/
lemma card_filter_subset_le_one_of_card_eq {α : Type*} [DecidableEq α]
    (k : ℕ) (ℱ : Finset (Finset α))
    (hunif : ∀ F ∈ ℱ, F.card = k)
    (A : Finset α) (hA : A.card = k) :
    (ℱ.filter (fun F => A ⊆ F)).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro F₁ F₂ h₁ h₂
  rw [Finset.mem_filter] at h₁ h₂
  have eqA (F : Finset α) (hF : F ∈ ℱ) (hsub : A ⊆ F) : F = A :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hunif F hF, hA])).symm
  rw [eqA F₁ h₁.1 h₁.2, eqA F₂ h₂.1 h₂.2]
