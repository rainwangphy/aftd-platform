import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MmsExistsMonotone
import AFTD.Kb.GameTheoryEconomics.Mms4GridValue
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.MaximinShare

/-!
# mms_two_agents_four_goods_not_exists

Topic: fair_division   Node: db63f2057add

Provenance: formalization of a published result. Source: arXiv:2610.06125 (On MMS allocations with few items), Table 1 (a well-known example recalled in Sec. 1)

With two agents, four goods and monotone valuations, an MMS allocation need not exist (both agents have MMS 2 in the Table 1 instance, but every allocation leaves one of them with value at most 1). Hence μ(2) ≤ 3.
-/

theorem mms4_grid_value_mono : ∀ i S T, S ⊆ T → mms4_grid_value i S ≤ mms4_grid_value i T := by
  decide

theorem mms4_grid_no_good_allocation :
    ∀ σ : Fin 4 → Fin 2, ∃ i, mms4_grid_value i (bundle_of σ i) ≤ 1 := by decide

theorem mms_two_agents_four_goods_not_exists : ¬ mms_exists_monotone 2 4 := by
  intro h
  obtain ⟨σ, hσ⟩ := h (fun i S => (mms4_grid_value i S : ℝ)) (fun i =>
    ⟨⟨by positivity, fun S T hST => Nat.cast_le.2 (mms4_grid_value_mono i S T hST)⟩,
      by simp [mms4_grid_value]⟩)
  have hm : ∀ i, (2 : ℝ) ≤ maximin_share (fun S => (mms4_grid_value i S : ℝ)) 2 := by
    intro i
    unfold maximin_share
    refine le_ciSup_of_le (Set.finite_range _).bddAbove
      (if i = 0 then ![0, 0, 1, 1] else ![0, 1, 0, 1]) (le_ciInf fun j => ?_)
    have : ∀ i j : Fin 2, 2 ≤ mms4_grid_value i
        (bundle_of (if i = 0 then ![0, 0, 1, 1] else ![0, 1, 0, 1]) j) := by decide
    show (2 : ℝ) ≤ (mms4_grid_value i _ : ℝ)
    exact_mod_cast this i j
  obtain ⟨i, hi⟩ := mms4_grid_no_good_allocation σ
  have h1 : (2 : ℝ) ≤ (mms4_grid_value i (bundle_of σ i) : ℝ) := (hm i).trans (hσ i)
  have h2 : (mms4_grid_value i (bundle_of σ i) : ℝ) ≤ 1 := by exact_mod_cast hi
  linarith
