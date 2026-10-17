import AFTD.Prelude
import AFTD.Kb.Tcs.LinearMapBilinFormContinuousISup

/-!
# LinearMap.BilinForm.continuous_iSup_fst

Topic: quantum   Node: af674475efca

Provenance: formalization of a published result. Source: QuantumInfo, `LinearMap.BilinForm.continuous_iSup_fst`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ContinuousSup.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearMap.BilinForm.continuous_iSup_fst
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α β γ : Type*} {S : Set β} {f : γ → β → α} in
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] in
variable [TopologicalSpace γ] in
theorem LinearMap.BilinForm.continuous_iSup_fst
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : LinearMap.BilinForm ℝ E) {S : Set E} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨆ y : S, f y x := by
  exact LinearMap.BilinForm.continuous_iSup f.flip hS
  --Old "direct" proof:
  -- -- Since $f$ is continuous, there exists $C > 0$ such that for all $y \in S$ and $x \in E$, $|f y x| \leq C \|y\| \|x\|$.
  -- obtain ⟨C, hC1, hC2⟩ : ∃ C > 0, ∀ y ∈ S, ∀ x : E, |f y x| ≤ C * ‖y‖ * ‖x‖ := by
  --   -- Since $f$ is continuous, there exists $C > 0$ such that for all $y, x \in E$, $|f y x| \leq C \|y\| \|x\|$ by the boundedness of continuous bilinear maps on finite-dimensional spaces.
  --   have h_cont : ∃ C > 0, ∀ y x : E, |f y x| ≤ C * ‖y‖ * ‖x‖ := by
  --     have h_bounded : Continuous (fun p : E × E => f p.1 p.2) := by
  --       have _ := isModuleTopologyOfFiniteDimensional (𝕜 := ℝ) (E := E)
  --       fun_prop
  --     obtain ⟨C, hC₀, hC⟩ : ∃ C > 0, ∀ y x : E, ‖y‖ ≤ 1 → ‖x‖ ≤ 1 → |f y x| ≤ C := by
  --       have h_compact : IsCompact {p : E × E | ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1} := by
  --         have h_closed_unit_ball : IsCompact {p : E | ‖p‖ ≤ 1} := by
  --           convert ProperSpace.isCompact_closedBall (0 : E) 1
  --           simp [Metric.closedBall, dist_eq_norm]
  --         exact h_closed_unit_ball.prod h_closed_unit_ball;
  --       obtain ⟨C, hC⟩ := h_compact.exists_bound_of_continuousOn h_bounded.continuousOn;
  --       exact ⟨C ⊔ 1, zero_lt_one.trans_le (le_max_right _ _), fun y x hy hx ↦ (hC (y, x) ⟨hy, hx⟩ ).trans (le_max_left _ _)⟩;
  --     refine ⟨C, hC₀, fun y x ↦ ?_⟩;
  --     rcases eq_or_ne y 0 with rfl | hy; · simp
  --     rcases eq_or_ne x 0 with rfl | hx; · simp
  --     have := hC (‖y‖⁻¹ • y) (‖x‖⁻¹ • x) (by simp [hy, norm_smul]) (by simp [hx, norm_smul])
  --     simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  --     rw [abs_le] at this ⊢
  --     rw [← norm_ne_zero_iff] at hx hy
  --     have : 0 < ‖y‖ * ‖x‖ := by positivity
  --     have := inv_mul_cancel_left₀ hy ((f y) x)
  --     have := inv_mul_cancel_left₀ hx ((f y) x)
  --     have := mul_inv_cancel₀ hy
  --     constructor <;> nlinarith
  --   exact ⟨ h_cont.choose, h_cont.choose_spec.1, fun y hy x ↦ h_cont.choose_spec.2 y x ⟩;
  -- -- Since $S$ is bounded, there exists $M > 0$ such that for all $y \in S$, $\|y\| \leq M$.
  -- obtain ⟨M, hM1, hM2⟩ : ∃ M > 0, ∀ y ∈ S, ‖y‖ ≤ M :=
  --   hS.exists_pos_norm_le
  -- rw [Metric.continuous_iff]
  -- intro b ε hε
  -- refine ⟨ε / (C * M + 1), div_pos hε (by positivity), fun a ha ↦ ?_⟩
  -- -- Using the triangle inequality and the continuity of $f$, we get:
  -- have h_triangle (y) (hy : y ∈ S) : |f y a - f y b| ≤ C * M * ‖a - b‖ := by
  --   rw [← map_sub]
  --   apply (hC2 y hy ( a - b )).trans
  --   refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  --   exact mul_le_mul_of_nonneg_left (hM2 y hy) hC1.le
  -- rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩; · simp [*]
  -- simp [dist_eq_norm] at *
  -- -- Applying the triangle inequality to the suprema, we get:
  -- have h_sup_triangle : |(⨆ y : S, f y a) - (⨆ y : S, f y b)| ≤ C * M * ‖a - b‖ := by
  --   rw [abs_sub_le_iff]
  --   constructor
  --   · -- Applying the inequality $f y a \leq f y b + C * M * ‖a - b‖$ to each term in the supremum, we get:
  --     have h_le (y : S) : f y a ≤ f y b + C * M * ‖a - b‖ := by
  --       linarith [abs_le.mp (h_triangle y y.2)]
  --     rw [sub_le_iff_le_add, add_comm]
  --     convert ciSup_le fun y => le_trans ( h_le y ) _;
  --     · exact ⟨⟨ y, hy ⟩⟩
  --     · refine add_le_add ?_ le_rfl
  --       refine le_csSup ?_ (Set.mem_range_self _)
  --       exact ⟨C * M * ‖b‖, Set.forall_mem_range.2 fun y => le_of_abs_le ((hC2 _ y.2 _).trans (by gcongr; exact hM2 _ y.2))⟩;
  --   · rw [sub_le_iff_le_add']
  --     -- Applying the triangle inequality to each term in the supremum, we get:
  --     have h_sup_triangle (y) (hy : y ∈ S) : f y b ≤ f y a + C * M * ‖a - b‖ := by
  --       linarith [abs_le.mp (h_triangle y hy)]
  --     convert ciSup_le _
  --     · exact ⟨⟨y, hy⟩⟩
  --     · intro x
  --       refine (h_sup_triangle x x.2).trans (add_le_add_left ?_ _)
  --       exact le_ciSup (show BddAbove (Set.range fun y : S ↦ f y a) by
  --         refine ⟨C * M * ‖a‖, Set.forall_mem_range.2 fun y ↦ ?_⟩
  --         refine le_of_abs_le ((hC2 _ y.2 _).trans ?_)
  --         refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  --         exact mul_le_mul_of_nonneg_left (hM2 _ y.2) hC1.le
  --       ) x;
  -- apply h_sup_triangle.trans_lt
  -- rw [lt_div_iff₀ (by positivity)] at ha
  -- nlinarith [mul_pos hC1 hM1]
