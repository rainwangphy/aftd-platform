import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPairBlocked
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_equal_pairs_few_blockers_ir_completion

Topic: fair_division   Node: 4b306b760f92

Provenance: helper lemma. step towards efx_allsource_equal_pairs_ir_completion

If some old pair p has at most one blocking agent, then some complete EFX allocation preserves all old utilities while leaving all four old pairs intact (a fortiori at least two).
-/

def efx_equal_pairs_few_blockers_ir_completion_pair_of_good (g : Fin 9) : Fin 4 :=
  ⟨(g.val / 2) % 4, by omega⟩

lemma efx_equal_pairs_few_blockers_ir_completion_pair_of_good_eq (p : Fin 4) (g : Fin 9) (hg : g ≠ 8) :
    efx_equal_pairs_few_blockers_ir_completion_pair_of_good g = p ↔ g = ![0,2,4,6] p ∨ g = ![1,3,5,7] p := by
  fin_cases g <;> fin_cases p
  all_goals
    first
    | contradiction
    | decide

def efx_equal_pairs_few_blockers_ir_completion_sigma (p m : Fin 4) (g : Fin 9) : Fin 4 :=
  if g = 8 then m else Equiv.swap p m (efx_equal_pairs_few_blockers_ir_completion_pair_of_good g)

lemma efx_equal_pairs_few_blockers_ir_completion_bundle_of_m (p m : Fin 4) :
    bundle_of (efx_equal_pairs_few_blockers_ir_completion_sigma p m) m = {![0,2,4,6] p, ![1,3,5,7] p, 8} := by
  ext g
  simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  dsimp [efx_equal_pairs_few_blockers_ir_completion_sigma]
  split_ifs with h8
  · subst h8
    simp
  · rw [← Equiv.eq_symm_apply, Equiv.symm_swap, Equiv.swap_apply_right]
    rw [efx_equal_pairs_few_blockers_ir_completion_pair_of_good_eq _ _ h8]
    simp [h8]

lemma efx_equal_pairs_few_blockers_ir_completion_bundle_of_ne_m (p m : Fin 4) (j : Fin 4) (hj : j ≠ m) :
    bundle_of (efx_equal_pairs_few_blockers_ir_completion_sigma p m) j =
      {![0,2,4,6] ((Equiv.swap p m) j), ![1,3,5,7] ((Equiv.swap p m) j)} := by
  ext g
  simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  dsimp [efx_equal_pairs_few_blockers_ir_completion_sigma]
  split_ifs with h8
  · subst h8
    have h8not : ¬ ((8 : Fin 9) = ![0, 2, 4, 6] ((Equiv.swap p m) j) ∨
                    (8 : Fin 9) = ![1, 3, 5, 7] ((Equiv.swap p m) j)) := by
      revert p m j
      decide
    simp only [hj.symm, false_iff]
    exact h8not
  · rw [← Equiv.eq_symm_apply, Equiv.symm_swap]
    rw [efx_equal_pairs_few_blockers_ir_completion_pair_of_good_eq _ _ h8]

lemma efx_equal_pairs_few_blockers_ir_completion_goods_distinct (q : Fin 4) :
    (![0,2,4,6] : Fin 4 → Fin 9) q ≠ ![1,3,5,7] q := by
  fin_cases q <;> decide

lemma efx_equal_pairs_few_blockers_ir_completion_goods_not_8_left (q : Fin 4) :
    (![0,2,4,6] : Fin 4 → Fin 9) q ≠ 8 := by
  fin_cases q <;> decide

lemma efx_equal_pairs_few_blockers_ir_completion_goods_not_8_right (q : Fin 4) :
    (![1,3,5,7] : Fin 4 → Fin 9) q ≠ 8 := by
  fin_cases q <;> decide

lemma efx_equal_pairs_few_blockers_ir_completion_erase_three_first (a b c : Fin 9) (hab : a ≠ b) (hac : a ≠ c) :
    ({a, b, c} : Finset (Fin 9)).erase a = {b, c} := by
  ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; aesop

lemma efx_equal_pairs_few_blockers_ir_completion_erase_three_second (a b c : Fin 9) (hab : a ≠ b) (hbc : b ≠ c) :
    ({a, b, c} : Finset (Fin 9)).erase b = {a, c} := by
  ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; aesop

lemma efx_equal_pairs_few_blockers_ir_completion_erase_three_third (a b c : Fin 9) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset (Fin 9)).erase c = {a, b} := by
  ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; aesop

lemma efx_equal_pairs_few_blockers_ir_completion_erase_two_first (a b : Fin 9) (hab : a ≠ b) :
    ({a, b} : Finset (Fin 9)).erase a = {b} := by
  ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; aesop

lemma efx_equal_pairs_few_blockers_ir_completion_erase_two_second (a b : Fin 9) (hab : a ≠ b) :
    ({a, b} : Finset (Fin 9)).erase b = {a} := by
  ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; aesop

lemma efx_equal_pairs_few_blockers_ir_completion_av_two (u : Fin 9 → ℝ) (a b : Fin 9) (hab : a ≠ b) :
    additive_valuation u {a, b} = u a + u b := by
  dsimp [additive_valuation]
  have h : a ∉ ({b} : Finset (Fin 9)) := by simp [hab]
  rw [Finset.sum_insert h, Finset.sum_singleton]

lemma efx_equal_pairs_few_blockers_ir_completion_av_one (u : Fin 9 → ℝ) (a : Fin 9) :
    additive_valuation u {a} = u a := by
  simp [additive_valuation]

lemma efx_equal_pairs_few_blockers_ir_completion_ir_holds (v : Fin 4 → Fin 9 → ℝ)
    (hpos : ∀ i g, 0 < v i g)
    (hequal : ∀ (i j : Fin 4),
      v i (![0,2,4,6] j) + v i (![1,3,5,7] j) =
        v i (![0,2,4,6] i) + v i (![1,3,5,7] i))
    (p m : Fin 4) (i : Fin 4) :
    v i (![0,2,4,6] i) + v i (![1,3,5,7] i) ≤
      additive_valuation (fun g => v i g) (bundle_of (efx_equal_pairs_few_blockers_ir_completion_sigma p m) i) := by
  by_cases hi : i = m
  · rw [hi, efx_equal_pairs_few_blockers_ir_completion_bundle_of_m]
    dsimp [additive_valuation]
    have h1 : (![0,2,4,6] : Fin 4 → Fin 9) p ∉ ({![1,3,5,7] p, 8} : Finset (Fin 9)) := by
      simp [efx_equal_pairs_few_blockers_ir_completion_goods_distinct p,
            efx_equal_pairs_few_blockers_ir_completion_goods_not_8_left p]
    have h2 : (![1,3,5,7] : Fin 4 → Fin 9) p ∉ ({8} : Finset (Fin 9)) := by
      simp [efx_equal_pairs_few_blockers_ir_completion_goods_not_8_right p]
    rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
    have := hequal m p
    have := hpos m 8
    linarith
  · rw [efx_equal_pairs_few_blockers_ir_completion_bundle_of_ne_m p m i hi]
    rw [efx_equal_pairs_few_blockers_ir_completion_av_two _ _ _
        (efx_equal_pairs_few_blockers_ir_completion_goods_distinct ((Equiv.swap p m) i))]
    have := hequal i ((Equiv.swap p m) i)
    linarith

lemma efx_equal_pairs_few_blockers_ir_completion_efx_holds (v : Fin 4 → Fin 9 → ℝ)
    (hpos : ∀ i g, 0 < v i g)
    (hequal : ∀ (i j : Fin 4),
      v i (![0,2,4,6] j) + v i (![1,3,5,7] j) =
        v i (![0,2,4,6] i) + v i (![1,3,5,7] i))
    (p m : Fin 4)
    (hpm : ∀ i : Fin 4, i ≠ m → ¬ efx_pair_blocked v i p) :
    is_efx_goods v (efx_equal_pairs_few_blockers_ir_completion_sigma p m) := by
  intro i j hij g hg
  apply le_trans _ (efx_equal_pairs_few_blockers_ir_completion_ir_holds v hpos hequal p m i)
  by_cases hj : j = m
  · rw [hj] at hg ⊢
    rw [efx_equal_pairs_few_blockers_ir_completion_bundle_of_m] at hg ⊢
    have h1 := efx_equal_pairs_few_blockers_ir_completion_goods_distinct p
    have h2 := efx_equal_pairs_few_blockers_ir_completion_goods_not_8_left p
    have h3 := efx_equal_pairs_few_blockers_ir_completion_goods_not_8_right p
    have hblock : ¬ efx_pair_blocked v i p := hpm i (by rwa [hj] at hij)
    simp only [efx_pair_blocked, not_or, not_lt] at hblock
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl
    · rw [efx_equal_pairs_few_blockers_ir_completion_erase_three_first _ _ _ h1 h2]
      rw [efx_equal_pairs_few_blockers_ir_completion_av_two _ _ _ h3]
      have := hequal i p
      linarith
    · rw [efx_equal_pairs_few_blockers_ir_completion_erase_three_second _ _ _ h1 h3]
      rw [efx_equal_pairs_few_blockers_ir_completion_av_two _ _ _ h2]
      have := hequal i p
      linarith
    · rw [efx_equal_pairs_few_blockers_ir_completion_erase_three_third _ _ _ h2 h3]
      rw [efx_equal_pairs_few_blockers_ir_completion_av_two _ _ _ h1]
      have := hequal i p
      linarith
  · rw [efx_equal_pairs_few_blockers_ir_completion_bundle_of_ne_m p m j hj] at hg ⊢
    have h1 := efx_equal_pairs_few_blockers_ir_completion_goods_distinct ((Equiv.swap p m) j)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · rw [efx_equal_pairs_few_blockers_ir_completion_erase_two_first _ _ h1,
          efx_equal_pairs_few_blockers_ir_completion_av_one]
      have := hequal i ((Equiv.swap p m) j)
      have := hpos i (![0,2,4,6] ((Equiv.swap p m) j))
      linarith
    · rw [efx_equal_pairs_few_blockers_ir_completion_erase_two_second _ _ h1,
          efx_equal_pairs_few_blockers_ir_completion_av_one]
      have := hequal i ((Equiv.swap p m) j)
      have := hpos i (![1,3,5,7] ((Equiv.swap p m) j))
      linarith

lemma efx_equal_pairs_few_blockers_ir_completion_sigma_pair (p m : Fin 4) (q : Fin 4) :
    efx_equal_pairs_few_blockers_ir_completion_sigma p m (![0,2,4,6] q) =
      efx_equal_pairs_few_blockers_ir_completion_sigma p m (![1,3,5,7] q) := by
  fin_cases q <;> rfl

/-- Easy branch: when some old pair has at most one blocker, an all-pairs-intact allocation is EFX and preserves every owner's utility. -/
theorem efx_equal_pairs_few_blockers_ir_completion (v : Fin 4 → Fin 9 → ℝ)
  (hpos : ∀ i g, 0 < v i g)
  (hequal : ∀ (i j : Fin 4),
    v i (![0,2,4,6] j) + v i (![1,3,5,7] j) =
      v i (![0,2,4,6] i) + v i (![1,3,5,7] i))
  (hsmall : ∀ i : Fin 4,
    v i 8 ≤ v i (![0,2,4,6] i) ∧ v i 8 ≤ v i (![1,3,5,7] i))
  (h : ∃ p m : Fin 4, ∀ i : Fin 4, i ≠ m → ¬ efx_pair_blocked v i p) :
  ∃ σ : Fin 9 → Fin 4,
    is_efx_goods v σ ∧
    (∀ i : Fin 4,
      v i (![0,2,4,6] i) + v i (![1,3,5,7] i) ≤
        additive_valuation (fun g => v i g) (bundle_of σ i)) ∧
    (∃ a b : Fin 4, a ≠ b ∧
      σ (![0,2,4,6] a) = σ (![1,3,5,7] a) ∧
      σ (![0,2,4,6] b) = σ (![1,3,5,7] b)) := by
  obtain ⟨p, m, hpm⟩ := h
  refine ⟨efx_equal_pairs_few_blockers_ir_completion_sigma p m,
    efx_equal_pairs_few_blockers_ir_completion_efx_holds v hpos hequal p m hpm,
    efx_equal_pairs_few_blockers_ir_completion_ir_holds v hpos hequal p m,
    0, 1, by decide,
    efx_equal_pairs_few_blockers_ir_completion_sigma_pair p m 0,
    efx_equal_pairs_few_blockers_ir_completion_sigma_pair p m 1⟩
