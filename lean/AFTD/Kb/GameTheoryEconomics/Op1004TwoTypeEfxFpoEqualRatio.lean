import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.IsFractionallyParetoOptimal
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.FpoOfItemwiseWeightedMax

/-!
# op_1004_two_type_efx_fpo_equal_ratio

Topic: fair_division   Node: 110e13ca937b

Provenance: helper lemma. knowledgebase, OP-1004

For any real number a > 1, every two-agent instance on a finite set of goods where each good is valued at a by both agents or at 1 by both agents admits an allocation that is EFX and fractionally Pareto optimal.
-/

lemma op_1004_additive_valuation_insert {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) (g : Fin m) (hg : g ∉ S) :
    additive_valuation u (insert g S) = additive_valuation u S + u g := by
  dsimp [additive_valuation]
  rw [Finset.sum_insert hg, add_comm]

lemma op_1004_additive_valuation_erase {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) (g : Fin m) (hg : g ∈ S) :
    additive_valuation u (S.erase g) = additive_valuation u S - u g := by
  dsimp [additive_valuation]
  exact Finset.sum_erase_eq_sub hg

lemma op_1004_not_mem_bundle_of_of_mem_bundle_of {m : ℕ} (σ : Fin m → Fin 2) (g : Fin m)
    (i j : Fin 2) (hij : i ≠ j) (hg : g ∈ bundle_of σ j) : g ∉ bundle_of σ i := by
  intro hgi
  simp only [bundle_of, Finset.mem_filter] at hg hgi
  have : σ g = j := hg.2
  have : σ g = i := hgi.2
  subst_vars
  exact hij rfl

lemma op_1004_bundle_of_update_0 {m : ℕ} (σ : Fin m → Fin 2) (g : Fin m) :
    bundle_of (Function.update σ g 0) 0 = insert g (bundle_of σ 0) := by
  ext x
  simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hx : x = g
  · subst hx
    simp [Function.update_self]
  · simp [hx]

lemma op_1004_bundle_of_update_1 {m : ℕ} (σ : Fin m → Fin 2) (g : Fin m) :
    bundle_of (Function.update σ g 0) 1 = (bundle_of σ 1).erase g := by
  ext x
  simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases hx : x = g
  · subst hx
    simp [Function.update_self]
  · simp [hx]

lemma op_1004_bundle_of_update_to_1_0 {m : ℕ} (σ : Fin m → Fin 2) (g : Fin m) :
    bundle_of (Function.update σ g 1) 0 = (bundle_of σ 0).erase g := by
  ext x
  simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases hx : x = g
  · subst hx
    simp [Function.update_self]
  · simp [hx]

lemma op_1004_bundle_of_update_to_1_1 {m : ℕ} (σ : Fin m → Fin 2) (g : Fin m) :
    bundle_of (Function.update σ g 1) 1 = insert g (bundle_of σ 1) := by
  ext x
  simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hx : x = g
  · subst hx
    simp [Function.update_self]
  · simp [hx]

lemma op_1004_obj_update_lt (m : ℕ) (u : Fin m → ℝ) (hu : ∀ g, 0 < u g)
    (σ : Fin m → Fin 2) (g : Fin m) (hg : g ∈ bundle_of σ 1)
    (hvio : additive_valuation u (bundle_of σ 0) < additive_valuation u ((bundle_of σ 1).erase g)) :
    |additive_valuation u (bundle_of (Function.update σ g 0) 0) -
     additive_valuation u (bundle_of (Function.update σ g 0) 1)| <
    |additive_valuation u (bundle_of σ 0) - additive_valuation u (bundle_of σ 1)| := by
  rw [op_1004_bundle_of_update_0, op_1004_bundle_of_update_1]
  have hg0 : g ∉ bundle_of σ 0 := op_1004_not_mem_bundle_of_of_mem_bundle_of σ g 0 1 (by decide) hg
  rw [op_1004_additive_valuation_insert u _ _ hg0]
  rw [op_1004_additive_valuation_erase u _ _ hg]
  rw [op_1004_additive_valuation_erase u _ _ hg] at hvio
  set V0 := additive_valuation u (bundle_of σ 0)
  set V1 := additive_valuation u (bundle_of σ 1)
  have hug := hu g
  have hlt : V0 - V1 < 0 := by linarith
  rw [abs_of_neg hlt]
  rw [abs_lt]
  constructor <;> linarith

lemma op_1004_obj_update_to_1_lt (m : ℕ) (u : Fin m → ℝ) (hu : ∀ g, 0 < u g)
    (σ : Fin m → Fin 2) (g : Fin m) (hg : g ∈ bundle_of σ 0)
    (hvio : additive_valuation u (bundle_of σ 1) < additive_valuation u ((bundle_of σ 0).erase g)) :
    |additive_valuation u (bundle_of (Function.update σ g 1) 0) -
     additive_valuation u (bundle_of (Function.update σ g 1) 1)| <
    |additive_valuation u (bundle_of σ 0) - additive_valuation u (bundle_of σ 1)| := by
  rw [op_1004_bundle_of_update_to_1_0, op_1004_bundle_of_update_to_1_1]
  have hg1 : g ∉ bundle_of σ 1 := op_1004_not_mem_bundle_of_of_mem_bundle_of σ g 1 0 (by decide) hg
  rw [op_1004_additive_valuation_erase u _ _ hg]
  rw [op_1004_additive_valuation_insert u _ _ hg1]
  rw [op_1004_additive_valuation_erase u _ _ hg] at hvio
  set V0 := additive_valuation u (bundle_of σ 0)
  set V1 := additive_valuation u (bundle_of σ 1)
  have hug := hu g
  have hpos : 0 < V0 - V1 := by linarith
  rw [abs_of_pos hpos]
  rw [abs_lt]
  constructor <;> linarith

/-- For equal ratios a = b > 1, two-type instances admit an EFX and fractionally Pareto optimal allocation. -/
theorem op_1004_two_type_efx_fpo_equal_ratio (a : ℝ) (ha : 1 < a)
    (m : ℕ) (u : Fin 2 → Fin m → ℝ)
    (hu : ∀ g, (u 0 g = a ∧ u 1 g = a) ∨ (u 0 g = 1 ∧ u 1 g = 1)) :
    ∃ σ : Fin m → Fin 2, is_efx_goods u σ ∧ is_fractionally_pareto_optimal u σ := by
  have hu_pos : ∀ g, 0 < u 0 g := by
    intro g
    rcases hu g with ⟨h0, -⟩ | ⟨h0, -⟩
    · rw [h0]; linarith
    · rw [h0]; norm_num
  have hu_eq : ∀ i S, additive_valuation (u i) S = additive_valuation (u 0) S := by
    intro i S
    fin_cases i
    · rfl
    · dsimp [additive_valuation]
      apply Finset.sum_congr rfl
      intro g _
      rcases hu g with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1]
  let obj (σ : Fin m → Fin 2) : ℝ :=
    |additive_valuation (u 0) (bundle_of σ 0) - additive_valuation (u 0) (bundle_of σ 1)|
  have hnonempty : (Finset.univ : Finset (Fin m → Fin 2)).Nonempty := Finset.univ_nonempty
  obtain ⟨σ, -, hmin⟩ := Finset.exists_min_image Finset.univ obj hnonempty
  refine ⟨σ, ?_, ?_⟩
  · intro i j hij
    simp_rw [hu_eq]
    fin_cases i <;> fin_cases j <;> try contradiction
    · intro g hg
      by_contra! hvio
      have hlt := op_1004_obj_update_lt m (u 0) hu_pos σ g hg hvio
      have hle := hmin (Function.update σ g 0) (Finset.mem_univ _)
      exact not_le_of_gt hlt hle
    · intro g hg
      by_contra! hvio
      have hlt := op_1004_obj_update_to_1_lt m (u 0) hu_pos σ g hg hvio
      have hle := hmin (Function.update σ g 1) (Finset.mem_univ _)
      exact not_le_of_gt hlt hle
  · apply fpo_of_itemwise_weighted_max (w := fun _ => 1)
    · intro i; norm_num
    · intro g j
      have heq : ∀ i1 i2 : Fin 2, u i1 g = u i2 g := by
        intro i1 i2
        have h01 : u 0 g = u 1 g := by
          rcases hu g with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1]
        fin_cases i1 <;> fin_cases i2 <;> try rfl
        · exact h01
        · exact h01.symm
      rw [heq j (σ g)]
