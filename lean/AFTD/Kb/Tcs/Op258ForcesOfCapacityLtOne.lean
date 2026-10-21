import AFTD.Prelude
import AFTD.Kb.Tcs.Op258MonoCliqueOfFiberGtTuran
import AFTD.Kb.Tcs.Op258CardFiberSum
import AFTD.Kb.Tcs.Op258ForcesTwo
import AFTD.Kb.Tcs.Op258Forces
import AFTD.Kb.Tcs.Op258Bounded
import AFTD.Kb.Tcs.Op258HasMonoClique
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_258_forces_of_capacity_lt_one

Topic: combinatorics   Node: d71e87a86be7

Provenance: helper lemma. step towards op_258_forces_step

If k ≥ 2 and Σ_i min(a_i, 1 - 1/(k-1)) < 1, then every a-bounded colouring of K_n for large n already contains a monochromatic K_k; i.e. a forces a monochromatic K_k.
-/

lemma op_258_forces_of_capacity_lt_one_turan_bound_le (n r : ℕ) (hr : 1 ≤ r) :
    (((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 : ℕ) : ℝ) ≤ (1 - 1 / (r : ℝ)) * (n.choose 2 : ℝ) + n := by
  have h1 : (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 =
      (SimpleGraph.turanGraph n r).edgeFinset.card := SimpleGraph.card_edgeFinset_turanGraph.symm
  rw [h1]
  have h2 := SimpleGraph.mul_card_edgeFinset_turanGraph_le (n := n) (r := r)
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have h2_real : 2 * (r : ℝ) * ((SimpleGraph.turanGraph n r).edgeFinset.card : ℝ) ≤ ((r - 1 : ℕ) : ℝ) * (n ^ 2 : ℝ) := by
    exact_mod_cast h2
  have hr_sub : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by push_cast [hr]; rfl
  rw [hr_sub] at h2_real
  have hdiv : ((SimpleGraph.turanGraph n r).edgeFinset.card : ℝ) ≤ ((r : ℝ) - 1) * (n ^ 2 : ℝ) / (2 * (r : ℝ)) := by
    exact (le_div_iff₀ (by positivity)).mpr (by linarith)
  have heq : ((r : ℝ) - 1) * (n ^ 2 : ℝ) / (2 * (r : ℝ)) = (1 - 1 / (r : ℝ)) * (n ^ 2 : ℝ) / 2 := by
    have : (r : ℝ) ≠ 0 := by positivity
    field_simp
  have h_mid : ((SimpleGraph.turanGraph n r).edgeFinset.card : ℝ) ≤ (1 - 1 / (r : ℝ)) * (n ^ 2 : ℝ) / 2 := by
    rwa [← heq]
  have hch : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ n
  have h_sq : (1 - 1 / (r : ℝ)) * (n ^ 2 : ℝ) / 2 = (1 - 1 / (r : ℝ)) * (n.choose 2 : ℝ) + (1 - 1 / (r : ℝ)) * (n : ℝ) / 2 := by
    rw [hch]
    ring
  rw [h_sq] at h_mid
  have hr_le : (1 : ℝ) / (r : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hr_pos]
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have : (1 - 1 / (r : ℝ)) * (n : ℝ) / 2 ≤ (n : ℝ) := by
    have h_nonneg : (n : ℝ) ≥ 0 := by positivity
    have : 1 - 1 / (r : ℝ) ≤ 1 := by
      have : 0 < (1 : ℝ) / (r : ℝ) := div_pos (by norm_num) hr_pos
      linarith
    nlinarith
  linarith

lemma op_258_forces_of_capacity_lt_one_card_le_two (k : ℕ) (hk : 3 ≤ k) (J_card : ℕ)
    (hJ : (J_card : ℝ) * (1 - 1 / ((k : ℝ) - 1)) ≤ 1) :
    (J_card : ℝ) ≤ 2 := by
  have hk_sub : (2 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have htheta : (1 / 2 : ℝ) ≤ 1 - 1 / ((k : ℝ) - 1) := by
    have : 1 / ((k : ℝ) - 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have : (J_card : ℝ) * (1 / 2) ≤ (J_card : ℝ) * (1 - 1 / ((k : ℝ) - 1)) := by
    have : 0 ≤ (J_card : ℝ) := by positivity
    nlinarith
  linarith

/-- Capacity test: if the capped profile sums below 1, the profile forces a monochromatic K_k. -/
theorem op_258_forces_of_capacity_lt_one (a : ℕ+ → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hcap : (∑' i : ℕ+, ENNReal.ofReal (min (a i) (1 - 1 / ((k : ℝ) - 1)))) < 1) :
    op_258_forces a k := by
  rcases eq_or_lt_of_le hk with rfl | hk3
  · exact op_258_forces_two a
  · set θ : ℝ := 1 - 1 / ((k : ℝ) - 1)
    have hk_sub : (2 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
      linarith
    have hθ_ge : (1 / 2 : ℝ) ≤ θ := by
      have : 1 / ((k : ℝ) - 1) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith
    have hθ_pos : 0 < θ := by linarith
    set S : ENNReal := ∑' i : ℕ+, ENNReal.ofReal (min (a i) θ)
    have hne : S ≠ ⊤ := ne_of_lt (hcap.trans_le le_top)
    have hS_lt : S.toReal < 1 := by
      have h_lt := (ENNReal.toReal_lt_toReal hne (by norm_num)).mpr hcap
      simpa using h_lt
    set ε : ℝ := 1 - S.toReal
    have hε : 0 < ε := by linarith
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (4 / ε + 5)
    use n₀
    intro n hn c hc
    by_contra h_no
    have hn_pos : 0 < (n : ℝ) := by
      have : 0 < 4 / ε + 5 := by positivity
      have : 4 / ε + 5 < (n : ℝ) := hn₀.trans_le (by exact_mod_cast hn)
      linarith
    have hn2 : 2 ≤ n := by
      have : (2 : ℝ) ≤ (n : ℝ) := by
        have : 0 < 4 / ε := div_pos (by norm_num) hε
        have : 4 / ε + 5 < (n : ℝ) := hn₀.trans_le (by exact_mod_cast hn)
        linarith
      exact_mod_cast this
    have hpos : 0 < (n.choose 2 : ℝ) := by
      have : 0 < n.choose 2 := Nat.choose_pos hn2
      exact_mod_cast this
    set r := k - 1
    have hr : 1 ≤ r := by omega
    have hr_add : r + 1 = k := by omega
    have hr_cast : (r : ℝ) = (k : ℝ) - 1 := by
      simpa using Nat.cast_sub (R := ℝ) (by omega : 1 ≤ k)
    have h_turan_i : ∀ i : ℕ+, (((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e => c e = i)).card : ℝ)
        ≤ θ * (n.choose 2 : ℝ) + n := by
      intro i
      have h_not_gt : ¬ ((Finset.univ.filter (fun e => c e = i)).card >
          (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2) := by
        intro h_gt
        have h_mono := op_258_mono_clique_of_fiber_gt_turan n r hr c i h_gt
        rw [hr_add] at h_mono
        exact h_no h_mono
      have h_le_turan : ((Finset.univ.filter (fun e => c e = i)).card : ℝ) ≤
          (((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 : ℕ) : ℝ) := by
        have : (Finset.univ.filter (fun e => c e = i)).card ≤
            (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 := by omega
        exact_mod_cast this
      have hturan := op_258_forces_of_capacity_lt_one_turan_bound_le n r hr
      rw [hr_cast] at hturan
      exact h_le_turan.trans hturan
    set U := Finset.univ.image c
    set J := U.filter (fun i => θ < a i)
    have ha_nonneg : ∀ i ∈ U, 0 ≤ a i := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨e, -, he⟩
      have hmem : e ∈ (Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e' => c e' = i) := by
        simp [he]
      have hcard : 1 ≤ ((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e' => c e' = i)).card :=
        Finset.card_pos.mpr ⟨e, hmem⟩
      have hcard_real : (1 : ℝ) ≤ (((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e' => c e' = i)).card : ℝ) := by
        exact_mod_cast hcard
      have hle_i := hc i
      have : 0 < a i * (n.choose 2 : ℝ) := by linarith
      exact nonneg_of_mul_nonneg_left (by linarith) hpos
    have hmin_nonneg : ∀ i ∈ U, 0 ≤ min (a i) θ := by
      intro i hi
      exact le_min (ha_nonneg i hi) (le_of_lt hθ_pos)
    have h1 : ∑ i ∈ U, ENNReal.ofReal (min (a i) θ) ≤ S := ENNReal.sum_le_tsum U
    have hne1 : (∑ i ∈ U, ENNReal.ofReal (min (a i) θ)) ≠ ⊤ := ne_of_lt (h1.trans_lt (hcap.trans_le le_top))
    have h_sum_le := (ENNReal.toReal_le_toReal hne1 hne).mpr h1
    rw [← ENNReal.ofReal_sum_of_nonneg hmin_nonneg] at h_sum_le
    rw [ENNReal.toReal_ofReal (Finset.sum_nonneg hmin_nonneg)] at h_sum_le
    have hJ_sub : J ⊆ U := Finset.filter_subset _ _
    have h_subsum : (∑ i ∈ J, min (a i) θ) ≤ ∑ i ∈ U, min (a i) θ :=
      Finset.sum_le_sum_of_subset_of_nonneg hJ_sub (fun i hi _ => hmin_nonneg i hi)
    have hJ_eq : ∀ i ∈ J, min (a i) θ = θ := by
      intro i hi
      have : θ < a i := (Finset.mem_filter.mp hi).2
      exact min_eq_right (le_of_lt this)
    have hJ_sum : (∑ i ∈ J, min (a i) θ) = (J.card : ℝ) * θ := by
      rw [Finset.sum_congr rfl hJ_eq, Finset.sum_const, nsmul_eq_mul]
    have hJ_le_S : (J.card : ℝ) * θ ≤ S.toReal := by
      linarith
    have hJ_le_two : (J.card : ℝ) ≤ 2 :=
      op_258_forces_of_capacity_lt_one_card_le_two k hk3 J.card (by linarith)
    have hJ_mul_le : (J.card : ℝ) * (n : ℝ) ≤ 2 * (n : ℝ) := by
      nlinarith
    set fib := fun i : ℕ+ => (((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e => c e = i)).card : ℝ)
    have hJ_fib : ∀ i ∈ J, fib i ≤ min (a i) θ * (n.choose 2 : ℝ) + n := by
      intro i hi
      rw [hJ_eq i hi]
      exact h_turan_i i
    have hnotJ_fib : ∀ i ∈ U.filter (fun x => ¬ (θ < a x)), fib i ≤ min (a i) θ * (n.choose 2 : ℝ) := by
      intro i hi
      have hnot : ¬ (θ < a i) := (Finset.mem_filter.mp hi).2
      have hle : a i ≤ θ := not_lt.mp hnot
      have heq : min (a i) θ = a i := min_eq_left hle
      rw [heq]
      exact hc i
    have h_fib_sum : ∑ i ∈ U, fib i ≤ (∑ i ∈ U, min (a i) θ) * (n.choose 2 : ℝ) + (J.card : ℝ) * (n : ℝ) := by
      have h1 : ∑ i ∈ U, fib i = (∑ i ∈ J, fib i) + ∑ i ∈ U.filter (fun x => ¬ (θ < a x)), fib i :=
        (Finset.sum_filter_add_sum_filter_not U (fun x => θ < a x) fib).symm
      have h2 : ∑ i ∈ U, min (a i) θ = (∑ i ∈ J, min (a i) θ) + ∑ i ∈ U.filter (fun x => ¬ (θ < a x)), min (a i) θ :=
        (Finset.sum_filter_add_sum_filter_not U (fun x => θ < a x) (fun i => min (a i) θ)).symm
      rw [h1, h2, add_mul]
      have s1 : ∑ i ∈ J, fib i ≤ ∑ i ∈ J, (min (a i) θ * (n.choose 2 : ℝ) + n) :=
        Finset.sum_le_sum hJ_fib
      have s2 : ∑ i ∈ U.filter (fun x => ¬ (θ < a x)), fib i ≤ ∑ i ∈ U.filter (fun x => ¬ (θ < a x)), (min (a i) θ * (n.choose 2 : ℝ)) :=
        Finset.sum_le_sum hnotJ_fib
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at s1
      rw [← Finset.sum_mul] at s1
      rw [← Finset.sum_mul] at s2
      linarith
    have h_card_fiber : ∑ i ∈ U, fib i = (n.choose 2 : ℝ) := op_258_card_fiber_sum n c
    have h_le_almost : (n.choose 2 : ℝ) ≤ S.toReal * (n.choose 2 : ℝ) + 2 * (n : ℝ) := by
      calc
        (n.choose 2 : ℝ) = ∑ i ∈ U, fib i := h_card_fiber.symm
        _ ≤ (∑ i ∈ U, min (a i) θ) * (n.choose 2 : ℝ) + (J.card : ℝ) * (n : ℝ) := h_fib_sum
        _ ≤ S.toReal * (n.choose 2 : ℝ) + 2 * (n : ℝ) := by
          have : (∑ i ∈ U, min (a i) θ) * (n.choose 2 : ℝ) ≤ S.toReal * (n.choose 2 : ℝ) := by
            nlinarith
          linarith
    have h_le_fin : ε * (n.choose 2 : ℝ) ≤ 2 * (n : ℝ) := by
      linarith
    have hch : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ n
    rw [hch] at h_le_fin
    have hn_gt : 4 / ε + 5 < (n : ℝ) := hn₀.trans_le (by exact_mod_cast hn)
    have h4 : 4 < ε * ((n : ℝ) - 1) := by
      have h1 : 4 / ε < (n : ℝ) - 1 := by linarith
      have h2 := (div_lt_iff₀ hε).mp h1
      linarith
    have : 2 * (n : ℝ) < ε * ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
      have : 4 * (n : ℝ) < ε * ((n : ℝ) - 1) * (n : ℝ) := by nlinarith
      linarith
    linarith
