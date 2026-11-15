import AFTD.Prelude
import AFTD.Kb.Physics.HardCoreWeightedVar
import AFTD.Kb.Physics.HardCoreWeightedClosedNeighborhoodBound

/-!
# op_1355_center_violation_of_partition_bounds

Topic: statistical_mechanics   Node: 850bab63a6db

Provenance: helper lemma. OP-1355, explicit induced-claw witness for necessity

A center-only observable violates the weighted local variance bound whenever the center activity is one, its partition weight is between 0 and 17/16, the partition function is at least 1331, and the positive closed-neighborhood denominator is at most 33.
-/

open scoped BigOperators

lemma op1355_witness_algebra_scratch (Z P D : ℝ)
    (hZ : (1331 : ℝ) ≤ Z) (hP : 0 ≤ P) (hPmax : P ≤ (17 : ℝ)/16)
    (hD : 0 < D) (hDmax : D ≤ 33) :
    P / Z - (P / Z)^2 < 1 / D^2 := by
  have hquot : P / Z ≤ (17 : ℝ) / 21296 := by
    calc
      P / Z ≤ ((17 : ℝ)/16) / 1331 := div_le_div₀ (by norm_num) hPmax (by norm_num) hZ
      _ = (17 : ℝ)/21296 := by norm_num
  have hDsq : D^2 ≤ (33 : ℝ)^2 := by nlinarith
  have hinv : 1 / (33 : ℝ)^2 ≤ 1 / D^2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hD) hDsq
  have hnumeric : (17 : ℝ)/21296 < 1/(33 : ℝ)^2 := by norm_num
  nlinarith [sq_nonneg (P/Z)]



lemma op1355_center_variance_scratch {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : V → ℝ) (c : V) :
    let fam : Finset (Finset V) := Finset.univ.filter fun I => G.IsIndepSet (I : Set V)
    let Z : ℝ := ∑ I ∈ fam, ∏ v ∈ I, lam v
    let P : ℝ := ∑ I ∈ fam.filter (fun I => c ∈ I), ∏ v ∈ I, lam v
    hardCoreWeightedVar G lam (fun x => if x = c then 1 else 0) = P/Z - (P/Z)^2 := by
  classical
  dsimp only
  unfold hardCoreWeightedVar
  simp only [Finset.sum_ite_eq']
  have hsum (k : ℕ) (hk : 0 < k) :
      (∑ I ∈ (Finset.univ.filter fun I : Finset V => G.IsIndepSet (I : Set V)),
        (∏ v ∈ I, lam v) * (if c ∈ I then (1 : ℝ) else 0)^k) =
      ∑ I ∈ ((Finset.univ.filter fun I : Finset V => G.IsIndepSet (I : Set V)).filter (fun I => c ∈ I)), ∏ v ∈ I, lam v := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro I hI
    by_cases hp : G.IsIndepSet (I : Set V) <;> by_cases hc : c ∈ I <;> simp [hp, hc, hk.ne']
  rw [hsum 2 (by omega)]
  have h1 :
      (∑ I ∈ (Finset.univ.filter fun I : Finset V => G.IsIndepSet (I : Set V)),
        (∏ v ∈ I, lam v) * (if c ∈ I then (1 : ℝ) else 0)) =
      ∑ I ∈ ((Finset.univ.filter fun I : Finset V => G.IsIndepSet (I : Set V)).filter (fun I => c ∈ I)), ∏ v ∈ I, lam v := by
    simpa using hsum 1 (by omega)
  rw [h1]

lemma op1355_center_bound_scratch {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : V → ℝ) (c : V) :
    hardCoreWeightedClosedNeighborhoodBound G lam (fun x => if x = c then 1 else 0) =
      lam c / (1 + ∑ u ∈ insert c (G.neighborFinset c), lam u)^2 := by
  classical
  simp only [hardCoreWeightedClosedNeighborhoodBound, ite_pow, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), ite_mul, one_mul, zero_mul, ite_div, zero_div, Finset.sum_ite_eq', Finset.mem_univ, if_true]

open scoped Classical BigOperators in
theorem op_1355_center_violation_of_partition_bounds {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : V → ℝ) (c : V)
    (hcent : lam c = 1)
    (hZ : (1331 : ℝ) ≤ ∑ I ∈ (Finset.univ.filter fun I : Finset V => G.IsIndepSet (I : Set V)), ∏ x ∈ I, lam x)
    (hP : 0 ≤ ∑ I ∈ (Finset.univ.filter fun I : Finset V => G.IsIndepSet (I : Set V) ∧ c ∈ I), ∏ x ∈ I, lam x)
    (hPmax : (∑ I ∈ (Finset.univ.filter fun I : Finset V => G.IsIndepSet (I : Set V) ∧ c ∈ I), ∏ x ∈ I, lam x) ≤ (17 : ℝ)/16)
    (hD : 0 < 1 + ∑ x ∈ insert c (G.neighborFinset c), lam x)
    (hDmax : 1 + (∑ x ∈ insert c (G.neighborFinset c), lam x) ≤ 33) :
    hardCoreWeightedVar G lam (fun x => if x = c then 1 else 0) <
      hardCoreWeightedClosedNeighborhoodBound G lam (fun x => if x = c then 1 else 0) := by
  classical
  rw [op1355_center_variance_scratch, op1355_center_bound_scratch, hcent]
  apply op1355_witness_algebra_scratch
  · exact hZ
  · simpa [Finset.filter_filter, and_comm] using hP
  · simpa [Finset.filter_filter, and_comm] using hPmax
  · exact hD
  · exact hDmax
