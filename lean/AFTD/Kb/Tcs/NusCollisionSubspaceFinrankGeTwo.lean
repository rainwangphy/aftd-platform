import AFTD.Prelude
import AFTD.Kb.Tcs.NusCollisionSubspace
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetUnorderedSumRepCount

/-!
# nus_collision_subspace_finrank_ge_two

Topic: combinatorics   Node: 6383474c313c

Provenance: helper lemma. step towards nus_min_card_ge_near_quadratic

For a NUS set A ⊆ Z/pZ, the space of F_p-valued collision-preserving functions on A has dimension at least 2: the constant functions and the label map a ↦ a are both collision-preserving, and they are linearly independent because A has at least two distinct elements.
-/

/-- The modular half of Hou-Yang Lemma 2.1: the F_p-collision kernel of a NUS set has dimension at least 2, i.e. the modular rank of the collision matrix is at most n-2. -/
theorem nus_collision_subspace_finrank_ge_two {p : ℕ} [Fact p.Prime] {A : Finset (ZMod p)}
    (hA : finset_has_no_unique_sums A) :
    2 ≤ Module.finrank (ZMod p) ↥(nus_collision_subspace p A) := by
  have hcard : 1 < A.card := by have h := hA.1; omega
  -- The 2-dimensional space of maps `a ↦ c 0 + c 1 * a`, i.e. affine-linear maps.
  let F : (Fin 2 → ZMod p) →ₗ[ZMod p] (↥A → ZMod p) :=
    { toFun := fun u a => u 0 + u 1 * (a : ZMod p)
      map_add' := by
        intro x y
        ext a
        simp only [Pi.add_apply]
        ring
      map_smul' := by
        intro r x
        ext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  -- Every such map is collision-preserving.
  have hmem : ∀ u : Fin 2 → ZMod p, F u ∈ nus_collision_subspace p A := fun u => by
    intro a b c d h
    show u 0 + u 1 * (a : ZMod p) + (u 0 + u 1 * (b : ZMod p))
        = u 0 + u 1 * (c : ZMod p) + (u 0 + u 1 * (d : ZMod p))
    linear_combination (u 1) * h
  let G : (Fin 2 → ZMod p) →ₗ[ZMod p] ↥(nus_collision_subspace p A) := F.codRestrict _ hmem
  have hG : ∀ u, (G u : ↥A → ZMod p) = F u := fun u => LinearMap.codRestrict_apply _ _ u
  -- Injectivity: two distinct points of A separate the coefficients.
  have hinj : Function.Injective G := by
    intro x y hxy
    have hF : F x = F y := by
      rw [← hG x, ← hG y, congrArg Subtype.val hxy]
    have hpt : ∀ a : ↥A, x 0 + x 1 * (a : ZMod p) = y 0 + y 1 * (a : ZMod p) := by
      intro a
      exact congrFun hF a
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
    have hd : (x 1 - y 1) * (a - b) = 0 := by
      have h1 := hpt ⟨a, ha⟩
      have h2 := hpt ⟨b, hb⟩
      linear_combination h1 - h2
    have hne : (a - b) ≠ 0 := sub_ne_zero.mpr hab
    have h1 : x 1 = y 1 := by
      rcases mul_eq_zero.mp hd with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hne
    have h0 : x 0 = y 0 := by
      have h := hpt ⟨a, ha⟩
      rw [h1] at h
      exact add_right_cancel h
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fin_fun] at hle
