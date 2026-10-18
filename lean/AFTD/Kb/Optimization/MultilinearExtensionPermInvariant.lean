import AFTD.Prelude
import AFTD.Kb.Optimization.MultilinearExtension

/-!
# multilinear_extension_perm_invariant

Topic: submodular   Node: b8727a2b99c7

Provenance: helper lemma. step towards matroid_symmetry_gap_lt_eight_seventeenths

If a set function f is invariant under a permutation σ of the ground set, then its multilinear extension is invariant under the corresponding permutation of the coordinates: F(σ(x)) = F(x).
-/

/-- The multilinear extension of a permutation-invariant set function is invariant under the coordinate permutation. -/
theorem multilinear_extension_perm_invariant {m : ℕ} (f : Finset (Fin m) → ℝ)
    (σ : Equiv.Perm (Fin m))
    (hinv : ∀ S : Finset (Fin m), f (S.map σ.toEmbedding) = f S) (x : Fin m → ℝ) :
    multilinear_extension f (fun u => x (σ⁻¹ u)) = multilinear_extension f x := by
  simp only [multilinear_extension]
  -- Invariance of `f` along `σ⁻¹`, derived from the hypothesis by applying it to `S.map σ⁻¹`.
  have hf : ∀ S : Finset (Fin m), f S = f (S.map σ.symm.toEmbedding) := by
    intro S
    have h := hinv (S.map σ.symm.toEmbedding)
    rwa [show (S.map σ.symm.toEmbedding).map σ.toEmbedding = S from by
      simp [Finset.map_map]] at h
  -- The `S`-product reindexes along `σ⁻¹ : S → S.map σ⁻¹`.
  have hprod : ∀ S : Finset (Fin m),
      ∏ u ∈ S, x (σ⁻¹ u) = ∏ u ∈ S.map σ.symm.toEmbedding, x u := by
    intro S
    refine Finset.prod_bij (fun u _ => σ⁻¹ u) ?_ ?_ ?_ ?_
    · intro u hu; exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
    · intro a _ b _ hab; exact σ.symm.injective hab
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
      exact ⟨a, ha, rfl⟩
    · intro a _; rfl
  -- Same for the complementary product, using `(S.map σ⁻¹)ᶜ = Sᶜ.map σ⁻¹`.
  have hprod' : ∀ S : Finset (Fin m),
      ∏ u ∈ Sᶜ, (1 - x (σ⁻¹ u)) = ∏ u ∈ (S.map σ.symm.toEmbedding)ᶜ, (1 - x u) := by
    intro S
    rw [show (S.map σ.symm.toEmbedding)ᶜ = Sᶜ.map σ.symm.toEmbedding from by ext u; simp]
    refine Finset.prod_bij (fun u _ => σ⁻¹ u) ?_ ?_ ?_ ?_
    · intro u hu; exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
    · intro a _ b _ hab; exact σ.symm.injective hab
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
      exact ⟨a, ha, rfl⟩
    · intro a _; rfl
  -- Finally reindex the whole sum over the bijection `S ↦ S.map σ⁻¹` of `Finset (Fin m)`.
  refine Finset.sum_bij' (fun S _ => S.map σ.symm.toEmbedding) (fun T _ => T.map σ.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro a _; simp
  · intro a _; simp
  · intro a _
    show (a.map σ.symm.toEmbedding).map σ.toEmbedding = a
    simp [Finset.map_map]
  · intro a _
    show (a.map σ.toEmbedding).map σ.symm.toEmbedding = a
    simp [Finset.map_map]
  · intro a _
    rw [hprod a, hprod' a, hf a]
