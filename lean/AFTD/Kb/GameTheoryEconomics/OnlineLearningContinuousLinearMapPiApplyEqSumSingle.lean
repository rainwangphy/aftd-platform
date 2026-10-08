import AFTD.Prelude

/-!
# OnlineLearning.continuousLinearMap_pi_apply_eq_sum_single

Topic: equilibria   Node: 057883cd0284

Provenance: helper lemma. TCSlib, `OnlineLearning.continuousLinearMap_pi_apply_eq_sum_single`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Coordinate expansion of a continuous linear functional. Let $\iota$ be a finite index set and let $L \colon \bbr^{\iota} \to \bbr$ be a
continuous linear functional. Writing $e_i$ for the standard basis vector whose $i$-th
coordinate is $1$ and whose other coordinates are $0$, every vector $z \in \bbr^{\iota}$
satisfies
\[
  L(z) \;=\; \sum_{i \in \iota} z_i \, L(e_i).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- A continuous linear functional `L` on a finite product `ι → ℝ` is determined by its coordinate coefficients: `L z = Σ_i z i · L(e_i)`, where `e_i` is the `i`-th standard basis vector. Those coefficients are what we normalize into probabilities. -/
lemma OnlineLearning.continuousLinearMap_pi_apply_eq_sum_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (z : ι → ℝ) :
    L z = ∑ i : ι, z i * L (Pi.single i (1 : ℝ)) := by
  rw [← ContinuousLinearMap.sum_comp_single (R := ℝ) (φ := fun _ : ι => ℝ) L z]
  apply Finset.sum_congr rfl
  intro i _
  change L (Pi.single (M := fun _ : ι => ℝ) i (z i)) =
    z i * L (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))
  have hsingle :
      Pi.single (M := fun _ : ι => ℝ) i (z i) =
        (z i) • Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ) := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [Pi.single_eq_of_ne hji]
  rw [hsingle, map_smul]
  simp [smul_eq_mul]
