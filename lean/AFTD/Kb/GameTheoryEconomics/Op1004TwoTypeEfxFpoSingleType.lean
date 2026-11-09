import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.IsFractionallyParetoOptimal
import AFTD.Kb.GameTheoryEconomics.Op1004TwoTypeEfxFpoEqualRatio
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.FpoOfItemwiseWeightedMax
import AFTD.Kb.Tcs.G

/-!
# op_1004_two_type_efx_fpo_single_type

Topic: fair_division   Node: 9ef14c4ae53c

Provenance: helper lemma. knowledgebase, OP-1004

For two agents and any finite set of identical goods valued at c > 0 by agent 0 and d > 0 by agent 1, there exists an allocation that is EFX and fractionally Pareto optimal.
-/

lemma op_1004_two_type_efx_fpo_single_type_val_le (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (m : ℕ) (u : Fin 2 → Fin m → ℝ)
    (hu : ∀ g, u 0 g = c ∧ u 1 g = d)
    (S T : Finset (Fin m))
    (h : additive_valuation (u 0) S ≤ additive_valuation (u 0) T) :
    additive_valuation (u 1) S ≤ additive_valuation (u 1) T := by
  have hu0 : u 0 = fun _ => c := funext fun g => (hu g).1
  have hu1 : u 1 = fun _ => d := funext fun g => (hu g).2
  rw [hu0] at h
  rw [hu1]
  dsimp [additive_valuation] at *
  simp only [Finset.sum_const, nsmul_eq_mul] at *
  have : (S.card : ℝ) ≤ T.card := by
    nlinarith
  nlinarith

/-- Instances with a single type of identical goods always admit an EFX and fractionally Pareto optimal allocation. -/
theorem op_1004_two_type_efx_fpo_single_type (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (m : ℕ) (u : Fin 2 → Fin m → ℝ)
    (hu : ∀ g, u 0 g = c ∧ u 1 g = d) :
    ∃ σ : Fin m → Fin 2, is_efx_goods u σ ∧ is_fractionally_pareto_optimal u σ := by
  have hu_pos : ∀ g, 0 < u 0 g := by
    intro g
    rw [(hu g).1]
    exact hc
  let obj (σ : Fin m → Fin 2) : ℝ :=
    |additive_valuation (u 0) (bundle_of σ 0) - additive_valuation (u 0) (bundle_of σ 1)|
  have hnonempty : (Finset.univ : Finset (Fin m → Fin 2)).Nonempty := Finset.univ_nonempty
  obtain ⟨σ, -, hmin⟩ := Finset.exists_min_image Finset.univ obj hnonempty
  refine ⟨σ, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> try contradiction
    · intro g hg
      by_contra! hvio
      have hlt := op_1004_obj_update_lt m (u 0) hu_pos σ g hg hvio
      have hle := hmin (Function.update σ g 0) (Finset.mem_univ _)
      exact not_le_of_gt hlt hle
    · intro g hg
      apply op_1004_two_type_efx_fpo_single_type_val_le c d hc hd m u hu
      by_contra! hvio
      have hlt := op_1004_obj_update_to_1_lt m (u 0) hu_pos σ g hg hvio
      have hle := hmin (Function.update σ g 1) (Finset.mem_univ _)
      exact not_le_of_gt hlt hle
  · let w : Fin 2 → ℝ := fun k => if k = 0 then 1 / c else 1 / d
    apply fpo_of_itemwise_weighted_max (w := w)
    · intro k
      fin_cases k <;> simp [w, hc, hd]
    · intro g k
      have hw : ∀ i : Fin 2, w i * u i g = 1 := by
        intro i
        fin_cases i
        · change (1 / c) * u 0 g = 1
          rw [(hu g).1]
          exact one_div_mul_cancel (ne_of_gt hc)
        · change (1 / d) * u 1 g = 1
          rw [(hu g).2]
          exact one_div_mul_cancel (ne_of_gt hd)
      rw [hw k, hw (σ g)]
