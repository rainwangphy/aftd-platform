import AFTD.Prelude

/-!
# deletion_antipodal_pairs_not_ulc

Topic: combinatorics   Node: e2c7339233d9

Provenance: helper lemma.

A hereditary five-element set family can satisfy the antipodal-pairs inequality on every even-sized deletion while its rank sequence fails ultra-log-concavity.
-/

theorem deletion_antipodal_pairs_not_ulc : ∃ F : Finset (Finset (Fin 5)), (∀ A ∈ F, ∀ B : Finset (Fin 5), B ⊆ A → B ∈ F) ∧ (let f := fun k : ℕ => (F.filter (fun S => S.card = k)).card; f 1 = 5 ∧ f 2 = 9 ∧ f 3 = 4 ∧ f 4 = 1) ∧ (∀ U : Finset (Fin 5), U.card = 2 → 2 * (U.powerset.filter (fun A => A.card = 0 ∧ A ∈ F ∧ U \ A ∈ F)).card ≤ (U.powerset.filter (fun A => A.card = 1 ∧ A ∈ F ∧ U \ A ∈ F)).card) ∧ (∀ U : Finset (Fin 5), U.card = 4 → 6 * (U.powerset.filter (fun A => A.card = 1 ∧ A ∈ F ∧ U \ A ∈ F)).card ≤ 4 * (U.powerset.filter (fun A => A.card = 2 ∧ A ∈ F ∧ U \ A ∈ F)).card) := ⟨(Finset.univ : Finset (Finset (Fin 5))).filter (fun S => 0 ∉ S ∨ (2 ∉ S ∧ ((S ∩ {1, 3, 4}).card ≤ 1))), by decide⟩
