import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSubmodular
import AFTD.Kb.Optimization.BlockPopulationCapacity
import AFTD.Kb.Optimization.ThermallyReachableBlockPopulations
import AFTD.Kb.Optimization.ThermallyReachableMicro
import AFTD.Kb.Optimization.FiberSumVec
import AFTD.Kb.Optimization.IsGibbsStochastic

/-!
# op_737_two_level_submodular

Topic: submodular   Node: b3253c7f4047

Provenance: helper lemma. arXiv:2610.35433 Sec. Discussion

For n > 2, any surjective block-assignment map proj : Fin n → Fin 2, any Gibbs vector γ in stdSimplex ℝ (Fin n) with strictly positive entries that is constant on the fibers of proj, and any initial vector x in stdSimplex ℝ (Fin n), the block population capacity block_population_capacity proj γ x is submodular.
-/

open Finset

lemma op_737_two_level_submodular_fin2_of_le (v : Finset (Fin 2) → ℝ)
    (h_univ : v univ + v ∅ ≤ v {0} + v {1}) :
    is_submodular v := by
  intro S T j hST hj
  have hT : ∀ (T : Finset (Fin 2)) (j : Fin 2), j ∉ T → T = ∅ ∨ T = {0} ∨ T = {1} := by
    decide
  rcases hT T j hj with rfl | rfl | rfl
  · have hS : S = ∅ := subset_empty.mp hST
    subst hS
    linarith
  · have hj0 : ∀ j : Fin 2, j ∉ ({0} : Finset (Fin 2)) → j = 1 := by decide
    have hj' := hj0 j hj
    subst hj'
    have hS : ∀ (S : Finset (Fin 2)), S ⊆ {0} → S = ∅ ∨ S = {0} := by decide
    rcases hS S hST with rfl | rfl
    · have hu : (insert (1 : Fin 2) {0} : Finset (Fin 2)) = univ := by decide
      have h1 : (insert (1 : Fin 2) (∅ : Finset (Fin 2)) : Finset (Fin 2)) = {1} := by decide
      rw [hu, h1]
      linarith
    · linarith
  · have hj1 : ∀ j : Fin 2, j ∉ ({1} : Finset (Fin 2)) → j = 0 := by decide
    have hj' := hj1 j hj
    subst hj'
    have hS : ∀ (S : Finset (Fin 2)), S ⊆ {1} → S = ∅ ∨ S = {1} := by decide
    rcases hS S hST with rfl | rfl
    · have hu : (insert (0 : Fin 2) {1} : Finset (Fin 2)) = univ := by decide
      have h0 : (insert (0 : Fin 2) (∅ : Finset (Fin 2)) : Finset (Fin 2)) = {0} := by decide
      rw [hu, h0]
      linarith
    · linarith

lemma op_737_two_level_submodular_capacity_empty {n m : ℕ} (proj : Fin n → Fin m) (γ x : Fin n → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin n)) :
    block_population_capacity proj γ x ∅ = 0 := by
  dsimp [block_population_capacity]
  have h_img : ((fun p => (0 : ℝ)) '' thermally_reachable_block_populations proj γ x) = {0} := by
    ext y
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rfl
    · rintro rfl
      have ⟨p, hp⟩ : (thermally_reachable_block_populations proj γ x).Nonempty := by
        use fiber_sum_vec proj x
        refine ⟨x, hx, ?_, rfl⟩
        use fun i j => if i = j then 1 else 0
        refine ⟨⟨fun i j => by dsimp; split_ifs <;> norm_num, fun j => by simp, fun i => by simp⟩, fun i => by simp⟩
      exact ⟨p, hp, rfl⟩
  rw [h_img, csSup_singleton]

lemma op_737_two_level_submodular_capacity_univ_le {n m : ℕ} (proj : Fin n → Fin m) (γ x : Fin n → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin n)) :
    block_population_capacity proj γ x univ ≤ 1 := by
  dsimp [block_population_capacity]
  apply csSup_le
  · rcases (by
      use fiber_sum_vec proj x
      refine ⟨x, hx, ?_, rfl⟩
      use fun i j => if i = j then 1 else 0
      refine ⟨⟨fun i j => by dsimp; split_ifs <;> norm_num, fun j => by simp, fun i => by simp⟩, fun i => by simp⟩ : (thermally_reachable_block_populations proj γ x).Nonempty) with ⟨p, hp⟩
    exact ⟨_, Set.mem_image_of_mem _ hp⟩
  · rintro y ⟨p, ⟨x', hx'sim, _, rfl⟩, rfl⟩
    dsimp [fiber_sum_vec]
    have h : ∑ k, ∑ i with proj i = k, x' i = ∑ i, x' i :=
      Finset.sum_fiberwise Finset.univ proj x'
    rw [h, hx'sim.2]

lemma op_737_two_level_submodular_capacity_bddAbove {n m : ℕ} (proj : Fin n → Fin m) (γ x : Fin n → ℝ)
    (S : Finset (Fin m)) :
    BddAbove ((fun p => ∑ k ∈ S, p k) '' thermally_reachable_block_populations proj γ x) := by
  use 1
  rintro y ⟨q, hq, rfl⟩
  rcases hq with ⟨x'', hx''sim, _, rfl⟩
  dsimp [fiber_sum_vec]
  have hp_nonneg : ∀ k, 0 ≤ ∑ i with proj i = k, x'' i :=
    fun k => Finset.sum_nonneg (fun i _ => hx''sim.1 i)
  have h_le_univ : ∑ k ∈ S, (∑ i with proj i = k, x'' i) ≤ ∑ k, (∑ i with proj i = k, x'' i) :=
    Finset.sum_le_univ_sum_of_nonneg (fun k => hp_nonneg k)
  rw [Finset.sum_fiberwise Finset.univ proj x'', hx''sim.2] at h_le_univ
  exact h_le_univ

lemma op_737_two_level_submodular_capacity_two_sum_ge {n : ℕ} (proj : Fin n → Fin 2) (γ x : Fin n → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin n)) :
    1 ≤ block_population_capacity proj γ x {0} + block_population_capacity proj γ x {1} := by
  have hp_mem : fiber_sum_vec proj x ∈ thermally_reachable_block_populations proj γ x := by
    refine ⟨x, hx, ?_, rfl⟩
    use fun i j => if i = j then 1 else 0
    refine ⟨⟨fun i j => by dsimp; split_ifs <;> norm_num, fun j => by simp, fun i => by simp⟩, fun i => by simp⟩
  have h0 : fiber_sum_vec proj x 0 ≤ block_population_capacity proj γ x {0} := by
    dsimp [block_population_capacity]
    have h_mem : fiber_sum_vec proj x 0 ∈ (fun p => ∑ k ∈ ({0} : Finset (Fin 2)), p k) '' thermally_reachable_block_populations proj γ x := by
      exact ⟨fiber_sum_vec proj x, hp_mem, by simp⟩
    exact le_csSup (op_737_two_level_submodular_capacity_bddAbove proj γ x {0}) h_mem
  have h1 : fiber_sum_vec proj x 1 ≤ block_population_capacity proj γ x {1} := by
    dsimp [block_population_capacity]
    have h_mem : fiber_sum_vec proj x 1 ∈ (fun p => ∑ k ∈ ({1} : Finset (Fin 2)), p k) '' thermally_reachable_block_populations proj γ x := by
      exact ⟨fiber_sum_vec proj x, hp_mem, by simp⟩
    exact le_csSup (op_737_two_level_submodular_capacity_bddAbove proj γ x {1}) h_mem
  have h_sum : fiber_sum_vec proj x 0 + fiber_sum_vec proj x 1 = 1 := by
    have h_tot : ∑ k : Fin 2, fiber_sum_vec proj x k = 1 := by
      dsimp [fiber_sum_vec]
      rw [Finset.sum_fiberwise Finset.univ proj x, hx.2]
    have h_split : ∑ k : Fin 2, fiber_sum_vec proj x k = fiber_sum_vec proj x 0 + fiber_sum_vec proj x 1 := by
      have h_univ : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
      rw [h_univ]
      simp
    linarith
  linarith

/-- For a two-level degenerate system, the block population capacity is submodular. -/
theorem op_737_two_level_submodular {n : ℕ} (hn : 2 < n) (proj : Fin n → Fin 2) (hsurj : Function.Surjective proj) (γ : Fin n → ℝ) (hγ_simplex : γ ∈ stdSimplex ℝ (Fin n)) (hγ_pos : ∀ i, 0 < γ i) (hγ_block : ∀ i j, proj i = proj j → γ i = γ j) (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) : is_submodular (block_population_capacity proj γ x) := by
  have _ := hn
  have _ := hsurj
  have _ := hγ_simplex
  have _ := hγ_pos
  have _ := hγ_block
  apply op_737_two_level_submodular_fin2_of_le
  have h_empty := op_737_two_level_submodular_capacity_empty proj γ x hx
  have h_univ := op_737_two_level_submodular_capacity_univ_le proj γ x hx
  have h_sum := op_737_two_level_submodular_capacity_two_sum_ge proj γ x hx
  linarith
