import AFTD.Prelude
import AFTD.Kb.Physics.Op2046Matrix
import AFTD.Kb.Physics.Op2046Spectrum
import AFTD.Kb.Physics.Op2046Majorizes
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.F

/-!
# op2046_wishart_majorization_event_measurable

Topic: quantum_mechanics   Node: e176f4eda55e

Provenance: helper lemma. Measurability sanity check for the Gaussian majorization event in OP-2046.

For every n, m, and h, the event that the first independent complex Gaussian Gram spectrum majorizes the second after normalization is measurable in the real and imaginary matrix coordinates, with zero-trace cases excluded.
-/

open Polynomial in
theorem in1074_eig_unique {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.IsHermitian)
    (μ : Fin (Fintype.card (Fin N)) → ℝ) (hμ : Antitone μ)
    (heq : ∀ s : ℝ, (Matrix.scalar (Fin N) (s : ℂ) - A).det = ∏ i, ((s : ℂ) - (μ i : ℂ))) :
    μ = hA.eigenvalues₀ := by
  have hp : A.charpoly = ∏ i, (X - C ((μ i : ℝ) : ℂ)) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := Set.range (fun s : ℝ => (s : ℂ)))
    · rintro _ ⟨s, rfl⟩
      simp only [Set.mem_ofPred_eq, Matrix.eval_charpoly, Polynomial.eval_prod, eval_sub, eval_X,
        eval_C]
      exact heq s
    · exact Set.infinite_range_of_injective Complex.ofReal_injective
  have hroots : A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ μ) Finset.univ.val := by
    rw [hp, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsort : (A.charpoly.roots.map RCLike.re).sort (· ≥ ·) = List.ofFn μ := by
    simp_rw [hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
      Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hμ.sortedGE_ofFn
  rw [hA.sort_roots_charpoly_eq_eigenvalues₀] at hsort
  exact (List.ofFn_inj.mp hsort).symm

theorem in1074_eig_measurable {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {N : ℕ}
    (A : X → Matrix (Fin N) (Fin N) ℂ) (hcont : Continuous A) (hH : ∀ x, (A x).IsHermitian)
    (k : Fin (Fintype.card (Fin N))) :
    Measurable (fun x => (hH x).eigenvalues₀ k) := by
  apply measurable_of_Iio
  intro t
  let F : Set (X × (Fin (Fintype.card (Fin N)) → ℝ)) :=
    (⋂ i, ⋂ j, ⋂ (_ : i ≤ j), {p | p.2 j ≤ p.2 i}) ∩
    ⋂ s : ℝ, {p | (Matrix.scalar (Fin N) (s : ℂ) - A p.1).det = ∏ i, ((s : ℂ) - (p.2 i : ℂ))}
  have hFc : IsClosed F := by
    apply IsClosed.inter
    · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le ((continuous_apply j).comp continuous_snd) ((continuous_apply i).comp continuous_snd)
    · exact isClosed_iInter fun s => isClosed_eq
        (Continuous.matrix_det (continuous_const.sub (hcont.comp continuous_fst)))
        (continuous_finsetProd _ (fun i _ => continuous_const.sub
          (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_snd))))
  have hmem : ∀ x μ, (x, μ) ∈ F ↔ μ = (hH x).eigenvalues₀ := by
    intro x μ
    constructor
    · rintro ⟨h1, h2⟩
      simp only [Set.mem_iInter, Set.mem_ofPred_eq] at h1 h2
      exact in1074_eig_unique (A x) (hH x) μ (fun i j hij => h1 i j hij) h2
    · rintro rfl
      refine ⟨?_, ?_⟩
      · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
        exact fun i j hij => (hH x).eigenvalues₀_antitone hij
      · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
        intro s
        rw [← Matrix.eval_charpoly, (hH x).charpoly_eq, Polynomial.eval_prod]
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
          Matrix.IsHermitian.eigenvalues]
        exact Fintype.prod_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm _ _
          (fun i => rfl)
  have hpre : (fun x => (hH x).eigenvalues₀ k) ⁻¹' Set.Iio t =
      Prod.fst '' (F ∩ {p | p.2 k < t}) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, (hH x).eigenvalues₀), ⟨(hmem x _).2 rfl, hx⟩, rfl⟩
    · rintro ⟨⟨y, μ⟩, ⟨hF, hlt⟩, rfl⟩
      rw [(hmem y μ).1 hF] at hlt
      exact hlt
  have hprec : ((fun x => (hH x).eigenvalues₀ k) ⁻¹' Set.Iio t)ᶜ =
      Prod.fst '' (F ∩ {p | t ≤ p.2 k}) := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Iio, not_lt] at hx
      exact ⟨(x, (hH x).eigenvalues₀), ⟨(hmem x _).2 rfl, hx⟩, rfl⟩
    · rintro ⟨⟨y, μ⟩, ⟨hF, hlt⟩, rfl⟩
      rw [(hmem y μ).1 hF] at hlt
      simpa using hlt
  apply MeasureTheory.AnalyticSet.measurableSet_of_compl
  · rw [hpre]
    exact (hFc.measurableSet.inter (measurableSet_lt
      ((measurable_pi_apply k).comp measurable_snd) measurable_const)).analyticSet.image_of_continuous
      continuous_fst
  · rw [hprec]
    exact (hFc.measurableSet.inter (measurableSet_le measurable_const
      ((measurable_pi_apply k).comp measurable_snd))).analyticSet.image_of_continuous
      continuous_fst

theorem in1074_matrix_continuous (n m : ℕ) : Continuous (op2046_matrix n m) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have h : (fun x : (Fin n × Fin m × Fin 2) → ℝ => op2046_matrix n m x i j) =
      fun x => ((x (i, j, 0) : ℝ) : ℂ) + ((x (i, j, 1) : ℝ) : ℂ) * Complex.I := by
    funext x
    simp only [op2046_matrix]
    exact Complex.mk_eq_add_mul_I _ _
  rw [h]
  fun_prop

theorem in1074_spectrum_measurable (n m : ℕ) (i : Fin n) :
    Measurable (fun x : (Fin n × Fin m × Fin 2) → ℝ => op2046_spectrum n m x i) := by
  have hc : Continuous (fun x => op2046_matrix n m x * (op2046_matrix n m x).conjTranspose) :=
    (in1074_matrix_continuous n m).matrix_mul (in1074_matrix_continuous n m).matrix_conjTranspose
  have := in1074_eig_measurable (fun x => op2046_matrix n m x * (op2046_matrix n m x).conjTranspose)
    hc (fun x => Matrix.isHermitian_mul_conjTranspose_self (op2046_matrix n m x))
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
  exact this

theorem op2046_wishart_majorization_event_measurable (n m h : ℕ) :
  MeasurableSet {z : ((Fin n × Fin m × Fin 2) → ℝ) × ((Fin n × Fin (m+h) × Fin 2) → ℝ) |
    op2046_majorizes n (op2046_spectrum n m z.1) (op2046_spectrum n (m+h) z.2)} := by
  have hx : ∀ i, Measurable (fun z : ((Fin n × Fin m × Fin 2) → ℝ) ×
      ((Fin n × Fin (m+h) × Fin 2) → ℝ) => op2046_spectrum n m z.1 i) :=
    fun i => (in1074_spectrum_measurable n m i).comp measurable_fst
  have hy : ∀ i, Measurable (fun z : ((Fin n × Fin m × Fin 2) → ℝ) ×
      ((Fin n × Fin (m+h) × Fin 2) → ℝ) => op2046_spectrum n (m+h) z.2 i) :=
    fun i => (in1074_spectrum_measurable n (m+h) i).comp measurable_snd
  have hsx : ∀ S : Finset (Fin n), Measurable (fun z : ((Fin n × Fin m × Fin 2) → ℝ) ×
      ((Fin n × Fin (m+h) × Fin 2) → ℝ) => ∑ i ∈ S, op2046_spectrum n m z.1 i) :=
    fun S => Finset.measurable_sum S (fun i _ => hx i)
  have hsy : ∀ S : Finset (Fin n), Measurable (fun z : ((Fin n × Fin m × Fin 2) → ℝ) ×
      ((Fin n × Fin (m+h) × Fin 2) → ℝ) => ∑ i ∈ S, op2046_spectrum n (m+h) z.2 i) :=
    fun S => Finset.measurable_sum S (fun i _ => hy i)
  unfold op2046_majorizes
  simp only [Set.ofPred_and, Set.ofPred_forall, Set.ofPred_exists]
  refine (measurableSet_lt measurable_const (hsx Finset.univ)).inter
    ((measurableSet_lt measurable_const (hsy Finset.univ)).inter ?_)
  refine MeasurableSet.iInter fun T => MeasurableSet.iUnion fun S => ?_
  exact (MeasurableSet.const _).inter (measurableSet_le ((hsy T).div (hsy Finset.univ))
    ((hsx S).div (hsx Finset.univ)))
