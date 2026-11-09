import AFTD.Prelude
import AFTD.Kb.Physics.HardCoreWeightedVar
import AFTD.Kb.Physics.HardCoreWeightedClosedNeighborhoodBound

/-!
# op_1355_complete_graph_variance_ge_bound

Topic: statistical_mechanics   Node: 6f003f3d0abf

Provenance: formalization of a published result. Source: OP-1355

On the complete graph (⊤ : SimpleGraph V) on a finite type V with decidable equality, for all positive vertex fugacities lam and all nonnegative observable weights a, the weighted hard-core variance hardCoreWeightedVar (⊤ : SimpleGraph V) lam a is at least the weighted closed-neighborhood bound hardCoreWeightedClosedNeighborhoodBound (⊤ : SimpleGraph V) lam a.
-/

lemma op_1355_complete_graph_weighted_cauchy_schwarz {V : Type*} (s : Finset V) (p q : V → ℝ) (hp : ∀ v ∈ s, 0 ≤ p v) :
    (∑ v ∈ s, p v * q v) ^ 2 ≤ (∑ v ∈ s, p v) * (∑ v ∈ s, p v * q v ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun v => Real.sqrt (p v)) (fun v => Real.sqrt (p v) * q v)
  have h1 : (∑ v ∈ s, (Real.sqrt (p v)) ^ 2) = ∑ v ∈ s, p v :=
    Finset.sum_congr rfl fun v hv => Real.sq_sqrt (hp v hv)
  have h2 : (∑ v ∈ s, (Real.sqrt (p v) * q v) ^ 2) = ∑ v ∈ s, p v * q v ^ 2 := by
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [mul_pow, Real.sq_sqrt (hp v hv)]
  have h3 : (∑ v ∈ s, Real.sqrt (p v) * (Real.sqrt (p v) * q v)) = ∑ v ∈ s, p v * q v := by
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hp v hv)]
  rw [h1, h2, h3] at h
  exact h

lemma op_1355_complete_graph_indep_top_eq {V : Type*} [Fintype V] [DecidableEq V] :
    ({I | (⊤ : SimpleGraph V).IsIndepSet (↑I : Set V)} : Finset (Finset V)) =
      insert ∅ (Finset.univ.image (fun v : V => ({v} : Finset V))) := by
  ext I
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image]
  constructor
  · intro h
    rcases Finset.eq_empty_or_nonempty I with rfl | ⟨v, hv⟩
    · left; rfl
    · right; refine ⟨v, ?_⟩
      ext u
      simp only [Finset.mem_singleton]
      constructor
      · rintro rfl; exact hv
      · intro hu
        by_contra hne
        exact h hu hv hne hne
  · rintro (rfl | ⟨v, rfl⟩)
    · intro u hu; simp at hu
    · intro u hu w hw hne
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hw
      subst hu hw
      exact (hne rfl).elim

lemma op_1355_complete_graph_empty_not_mem_image_singleton {V : Type*} [Fintype V] [DecidableEq V] :
    (∅ : Finset V) ∉ Finset.univ.image (fun v : V => ({v} : Finset V)) := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  rintro ⟨v, hv⟩
  exact Finset.ne_empty_of_mem (Finset.mem_singleton_self v) hv

lemma op_1355_complete_graph_sum_top_indep_lam {V : Type*} [Fintype V] [DecidableEq V] (lam : V → ℝ) :
    (∑ I ∈ ({I | (⊤ : SimpleGraph V).IsIndepSet (↑I : Set V)} : Finset (Finset V)), ∏ v ∈ I, lam v) =
      1 + ∑ v, lam v := by
  rw [op_1355_complete_graph_indep_top_eq, Finset.sum_insert op_1355_complete_graph_empty_not_mem_image_singleton]
  simp only [Finset.prod_empty]
  congr 1
  rw [Finset.sum_image Finset.singleton_injective.injOn]
  simp only [Finset.prod_singleton]

lemma op_1355_complete_graph_sum_top_indep_lam_mul_a {V : Type*} [Fintype V] [DecidableEq V] (lam a : V → ℝ) :
    (∑ I ∈ ({I | (⊤ : SimpleGraph V).IsIndepSet (↑I : Set V)} : Finset (Finset V)),
      (∏ v ∈ I, lam v) * ∑ v ∈ I, a v) =
      ∑ v, lam v * a v := by
  rw [op_1355_complete_graph_indep_top_eq, Finset.sum_insert op_1355_complete_graph_empty_not_mem_image_singleton]
  simp only [Finset.prod_empty, Finset.sum_empty, mul_zero, zero_add]
  rw [Finset.sum_image Finset.singleton_injective.injOn]
  simp only [Finset.prod_singleton, Finset.sum_singleton]

lemma op_1355_complete_graph_sum_top_indep_lam_mul_sq {V : Type*} [Fintype V] [DecidableEq V] (lam a : V → ℝ) :
    (∑ I ∈ ({I | (⊤ : SimpleGraph V).IsIndepSet (↑I : Set V)} : Finset (Finset V)),
      (∏ v ∈ I, lam v) * (∑ v ∈ I, a v) ^ 2) =
      ∑ v, lam v * (a v) ^ 2 := by
  rw [op_1355_complete_graph_indep_top_eq, Finset.sum_insert op_1355_complete_graph_empty_not_mem_image_singleton]
  simp only [Finset.prod_empty, Finset.sum_empty, sq, mul_zero, zero_add]
  rw [Finset.sum_image Finset.singleton_injective.injOn]
  simp only [Finset.prod_singleton, Finset.sum_singleton]

lemma op_1355_complete_graph_closed_neighborhood_top_bound {V : Type*} [Fintype V] [DecidableEq V]
    (lam a : V → ℝ) :
    hardCoreWeightedClosedNeighborhoodBound (⊤ : SimpleGraph V) lam a =
      (∑ v, lam v * a v ^ 2) / (1 + ∑ u, lam u) ^ 2 := by
  unfold hardCoreWeightedClosedNeighborhoodBound
  have h_nhbr : ∀ v : V, insert v ((⊤ : SimpleGraph V).neighborFinset v) = Finset.univ := by
    intro v
    ext u
    simp
  simp_rw [h_nhbr]
  rw [← Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun v _ => mul_comm _ _

lemma op_1355_complete_graph_hard_core_weighted_var_top {V : Type*} [Fintype V] [DecidableEq V]
    (lam a : V → ℝ) :
    hardCoreWeightedVar (⊤ : SimpleGraph V) lam a =
      (∑ v, lam v * a v ^ 2) / (1 + ∑ v, lam v) -
        ((∑ v, lam v * a v) / (1 + ∑ v, lam v)) ^ 2 := by
  unfold hardCoreWeightedVar
  dsimp only
  rw [op_1355_complete_graph_sum_top_indep_lam, op_1355_complete_graph_sum_top_indep_lam_mul_a, op_1355_complete_graph_sum_top_indep_lam_mul_sq]

lemma op_1355_complete_graph_div_sq_le_div_sub_div_sq (S M1 M2 : ℝ) (hS : 0 ≤ S)
    (hCS : M1 ^ 2 ≤ S * M2) :
    M2 / (1 + S) ^ 2 ≤ M2 / (1 + S) - (M1 / (1 + S)) ^ 2 := by
  have hpos : 0 < 1 + S := by linarith
  have hpos2 : 0 < (1 + S) ^ 2 := by positivity
  rw [div_pow]
  have h_eq : M2 / (1 + S) = (M2 * (1 + S)) / (1 + S) ^ 2 := by
    rw [sq]
    exact (mul_div_mul_right M2 (1 + S) (ne_of_gt hpos)).symm
  rw [h_eq, ← sub_div, div_le_div_iff_of_pos_right hpos2]
  calc M2 = M2 * 1 := (mul_one M2).symm
  _ ≤ M2 * 1 + (S * M2 - M1 ^ 2) := by linarith
  _ = M2 * (1 + S) - M1 ^ 2 := by ring

/-- On a complete graph, the weighted hard-core variance is at least the weighted closed-neighborhood bound by Cauchy-Schwarz. -/
theorem op_1355_complete_graph_variance_ge_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (lam : V → ℝ) (hlam : ∀ v, 0 < lam v) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    hardCoreWeightedClosedNeighborhoodBound (⊤ : SimpleGraph V) lam a ≤
      hardCoreWeightedVar (⊤ : SimpleGraph V) lam a := by
  rw [op_1355_complete_graph_closed_neighborhood_top_bound, op_1355_complete_graph_hard_core_weighted_var_top]
  apply op_1355_complete_graph_div_sq_le_div_sub_div_sq
  · exact Finset.sum_nonneg fun v _ => le_of_lt (hlam v)
  · exact op_1355_complete_graph_weighted_cauchy_schwarz Finset.univ lam a fun v _ => le_of_lt (hlam v)
