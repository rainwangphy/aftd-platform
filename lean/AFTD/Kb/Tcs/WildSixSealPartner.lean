import AFTD.Prelude

/-!
# wild_six_seal_partner

Topic: graphs   Node: 54dadae833ea

Provenance: helper lemma. step towards wild_normalized_array_disjoint_six_seal_mass_bound

For a row-injective array A on Fin N, the i-partner of a vertex x is the unique y with A x y = i; defined as the row-inverse (A x)⁻¹ i using the bijectivity of each row.
-/

/-- i-partner of x: the row-inverse of x applied to i. -/
noncomputable def wild_six_seal_partner {N : ℕ} (A : Fin N → Fin N → Fin N)
    (hinj : ∀ x, Function.Injective (A x)) (i x : Fin N) : Fin N := (Equiv.ofBijective (A x) ⟨hinj x, Finite.surjective_of_injective (hinj x)⟩).symm i
