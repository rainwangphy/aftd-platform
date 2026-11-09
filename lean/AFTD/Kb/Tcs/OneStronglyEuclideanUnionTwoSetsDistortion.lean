import AFTD.Prelude
import AFTD.Kb.Tcs.IsOneStronglyEuclidean
import AFTD.Kb.Tcs.EmbedsIntoHilbertWithDistortion

/-!
# one_strongly_euclidean_union_two_sets_distortion

Topic: algorithms   Node: 019cc47a6037

Provenance: formalization of a published result. Source: arXiv:2611.08546, Sec. 1.1

There exists an absolute constant C > 0 such that every metric space X that is the union of two subsets U_1, U_2, each 1-strongly Euclidean in X, embeds into a real Hilbert space with distortion at most C.
-/

theorem ose_var_identity {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (hc : ∑ i, c i = 1) (w : ι → F) :
    ∑ i, ∑ j, c i * c j * ‖w i - w j‖ ^ 2
      = 2 * ∑ i, c i * ‖w i‖ ^ 2 - 2 * ‖∑ i, c i • w i‖ ^ 2 := by
  have h1 : ‖∑ i, c i • w i‖ ^ 2 = ∑ i, ∑ j, c i * c j * inner ℝ (w i) (w j) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    ring
  have h2 : ∀ i j, ‖w i - w j‖ ^ 2 = ‖w i‖ ^ 2 - 2 * inner ℝ (w i) (w j) + ‖w j‖ ^ 2 :=
    fun i j => norm_sub_sq_real _ _
  have h3 : ∑ i, ∑ j, c i * c j * ‖w i‖ ^ 2 = ∑ i, c i * ‖w i‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, hc, mul_one]
  have h4 : ∑ i, ∑ j, c i * c j * ‖w j‖ ^ 2 = ∑ j, c j * ‖w j‖ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul, hc, one_mul]
  have h5 : ∀ i j, c i * c j * ‖w i - w j‖ ^ 2
      = c i * c j * ‖w i‖ ^ 2 - 2 * (c i * c j * inner ℝ (w i) (w j))
        + c i * c j * ‖w j‖ ^ 2 := fun i j => by rw [h2]; ring
  rw [h1]
  simp_rw [h5, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [h3, h4]
  ring

theorem ose_kirszbraun_finite {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (L : ℝ) (hL : 0 ≤ L)
    (x : ι → E) (y : ι → F) (z : E)
    (h : ∀ i j, ‖y i - y j‖ ≤ L * ‖x i - x j‖) :
    ∃ p : F, ∀ i, ‖p - y i‖ ≤ L * ‖z - x i‖ := by
  classical
  let v : ι → E := fun i => x i - z
  let a : ι → ℝ := fun i => ‖y i‖ ^ 2 - L ^ 2 * ‖v i‖ ^ 2
  let g : (ι → ℝ) → ℝ := fun c => ∑ i, c i * a i - ‖∑ i, c i • y i‖ ^ 2
  have hg : Continuous g := by
    apply Continuous.sub
    · exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
    · exact (continuous_norm.comp
        (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const)).pow 2
  obtain ⟨c, hc, hmax⟩ := (isCompact_stdSimplex ℝ ι).exists_isMaxOn
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary ι)⟩ hg.continuousOn
  have hcsum : ∑ i, c i = 1 := hc.2
  have hc0 : ∀ i, 0 ≤ c i := hc.1
  set p : F := ∑ i, c i • y i with hp
  set A : ℝ := ∑ i, c i * a i with hA
  -- the value at the maximum is nonpositive
  have hval : A - ‖p‖ ^ 2 ≤ 0 := by
    have e1 := ose_var_identity c hcsum y
    have e2 := ose_var_identity c hcsum v
    have hle : ∑ i, ∑ j, c i * c j * ‖y i - y j‖ ^ 2
        ≤ ∑ i, ∑ j, c i * c j * (L ^ 2 * ‖v i - v j‖ ^ 2) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hc0 i) (hc0 j))
      have hvv : v i - v j = x i - x j := by simp [v]
      rw [hvv]
      calc ‖y i - y j‖ ^ 2 ≤ (L * ‖x i - x j‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
        _ = L ^ 2 * ‖x i - x j‖ ^ 2 := by ring
    have e3 : ∑ i, ∑ j, c i * c j * (L ^ 2 * ‖v i - v j‖ ^ 2)
        = L ^ 2 * ∑ i, ∑ j, c i * c j * ‖v i - v j‖ ^ 2 := by
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have e4 : A = ∑ i, c i * ‖y i‖ ^ 2 - L ^ 2 * ∑ i, c i * ‖v i‖ ^ 2 := by
      rw [hA, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [a]
      ring
    have e5 : 0 ≤ L ^ 2 * ‖∑ i, c i • v i‖ ^ 2 := by positivity
    rw [e3, e2] at hle
    rw [e1] at hle
    rw [e4]
    nlinarith
  refine ⟨p, fun j => ?_⟩
  -- first-order condition at `j`
  have hfirst : a j - A - 2 * inner ℝ p (y j - p) ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    set S := a j - A - 2 * inner ℝ p (y j - p) with hS
    set M := ‖y j - p‖ ^ 2 with hM
    have hM0 : 0 ≤ M := by positivity
    set t : ℝ := S / (S + M + 1) with ht
    have hden : 0 < S + M + 1 := by linarith
    have ht0 : 0 < t := div_pos hcon hden
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith
    have htM : t * M < S := by
      rw [ht, div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    let c' : ι → ℝ := (1 - t) • c + t • Pi.single j (1 : ℝ)
    have hc' : c' ∈ stdSimplex ℝ ι :=
      convex_stdSimplex ℝ ι hc (single_mem_stdSimplex ℝ j) (by linarith) ht0.le (by ring)
    have hle := hmax hc'
    have e1 : ∑ i, c' i * a i = (1 - t) * A + t * a j := by
      simp only [c', Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
      rw [hA, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · simp [Pi.single_apply]
    have e2 : ∑ i, c' i • y i = p + t • (y j - p) := by
      simp only [c', Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
        mul_smul]
      rw [← Finset.smul_sum, ← Finset.smul_sum, ← hp]
      simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      simp only [smul_sub, sub_smul, one_smul]
      abel
    have e3 : ‖p + t • (y j - p)‖ ^ 2
        = ‖p‖ ^ 2 + 2 * t * inner ℝ p (y j - p) + t ^ 2 * M := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have hle' : (1 - t) * A + t * a j - ‖p + t • (y j - p)‖ ^ 2 ≤ A - ‖p‖ ^ 2 := by
      have := hle
      simp only [Set.mem_ofPred_eq, g] at this
      rw [e1, e2] at this
      exact this
    rw [e3] at hle'
    have : t * S ≤ t * (t * M) := by
      have : t * S = t * a j - t * A - 2 * t * inner ℝ p (y j - p) := by rw [hS]; ring
      nlinarith
    have := le_of_mul_le_mul_left this ht0
    linarith
  -- conclude
  have hsq : ‖p - y j‖ ^ 2 ≤ (L * ‖z - x j‖) ^ 2 := by
    have e1 : ‖p - y j‖ ^ 2 = ‖y j‖ ^ 2 - 2 * inner ℝ (y j) p + ‖p‖ ^ 2 := by
      rw [norm_sub_rev, norm_sub_sq_real]
    have e2 : inner ℝ p (y j - p) = inner ℝ (y j) p - ‖p‖ ^ 2 := by
      rw [inner_sub_right, real_inner_comm, real_inner_self_eq_norm_sq]
    have e3 : ‖v j‖ = ‖z - x j‖ := by simp [v, norm_sub_rev]
    have e4 : a j = ‖y j‖ ^ 2 - L ^ 2 * ‖z - x j‖ ^ 2 := by simp only [a, e3]
    rw [mul_pow]
    rw [e2, e4] at hfirst
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _)) (by norm_num)).1 hsq

theorem ose_fip {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {I : Type*} (y : I → F) (ρ : I → ℝ)
    (h : ∀ s : Finset I, ∃ p : F, ∀ i ∈ s, ‖p - y i‖ ≤ ρ i) :
    ∃ p : F, ∀ i, ‖p - y i‖ ≤ ρ i := by
  classical
  by_cases hI : Nonempty I
  swap
  · exact ⟨0, fun i => (hI ⟨i⟩).elim⟩
  obtain ⟨i₀⟩ := hI
  let C : Finset I → Set F := fun s => ⋂ i ∈ s, Metric.closedBall (y i) (ρ i)
  have hmemC : ∀ s p, p ∈ C s ↔ ∀ i ∈ s, ‖p - y i‖ ≤ ρ i := by
    intro s p
    simp [C, Metric.mem_closedBall, dist_eq_norm]
  have hCne : ∀ s, (C s).Nonempty := fun s => by
    obtain ⟨p, hp⟩ := h s
    exact ⟨p, (hmemC s p).2 hp⟩
  have hCclosed : ∀ s, IsClosed (C s) :=
    fun s => isClosed_biInter fun i _ => Metric.isClosed_closedBall
  have hCconv : ∀ s, Convex ℝ (C s) :=
    fun s => convex_iInter₂ fun i _ => convex_closedBall _ _
  have hmin : ∀ s, ∃ m ∈ C s, ∀ w ∈ C s, ‖m‖ ≤ ‖w‖ := by
    intro s
    obtain ⟨m, hm, hmeq⟩ :=
      exists_norm_eq_iInf_of_complete_convex (hCne s) (hCclosed s).isComplete (hCconv s) (0 : F)
    refine ⟨m, hm, fun w hw => ?_⟩
    have hb : BddBelow (Set.range fun w : C s => ‖(0 : F) - w‖) :=
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    have := ciInf_le hb (⟨w, hw⟩ : C s)
    simp only [zero_sub, norm_neg] at hmeq this
    linarith
  choose m hmC hmmin using hmin
  have hsub : ∀ {s t : Finset I}, s ⊆ t → C t ⊆ C s := by
    intro s t hst p hp
    exact (hmemC s p).2 fun i hi => (hmemC t p).1 hp i (hst hi)
  have hmono : ∀ {s t : Finset I}, s ⊆ t → ‖m s‖ ≤ ‖m t‖ :=
    fun hst => hmmin _ _ (hsub hst (hmC _))
  have hbd : ∀ s, ‖m s‖ ≤ ‖y i₀‖ + ρ i₀ := by
    intro s
    have h1 : ‖m s‖ ≤ ‖m (insert i₀ s)‖ := hmono (Finset.subset_insert _ _)
    have h2 := (hmemC _ _).1 (hmC (insert i₀ s)) i₀ (Finset.mem_insert_self _ _)
    have h3 : ‖m (insert i₀ s)‖ ≤ ‖m (insert i₀ s) - y i₀‖ + ‖y i₀‖ := by
      simpa using norm_add_le (m (insert i₀ s) - y i₀) (y i₀)
    linarith
  have hbdd : BddAbove (Set.range fun s => ‖m s‖ ^ 2) := by
    refine ⟨(‖y i₀‖ + ρ i₀) ^ 2, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd s) 2
  set S : ℝ := ⨆ s, ‖m s‖ ^ 2 with hS
  have hcauchy : CauchySeq m := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hlt : S - ε ^ 2 / 2 < S := by nlinarith [sq_pos_of_pos hε]
    obtain ⟨N, hN⟩ := exists_lt_of_lt_ciSup hlt
    refine ⟨N, fun n hn => ?_⟩
    have hNn : N ⊆ n := hn
    have hmid : (1 / 2 : ℝ) • m n + (1 / 2 : ℝ) • m N ∈ C N :=
      hCconv N (hsub hNn (hmC n)) (hmC N) (by norm_num) (by norm_num) (by norm_num)
    have h1 := hmmin N _ hmid
    have h2 : (1 / 2 : ℝ) • m n + (1 / 2 : ℝ) • m N = (1 / 2 : ℝ) • (m n + m N) := by
      rw [smul_add]
    rw [h2, norm_smul] at h1
    simp only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1
    have h3 := parallelogram_law_with_norm ℝ (m n) (m N)
    have hle : ‖m n‖ ^ 2 ≤ S := le_ciSup hbdd n
    have h4 : 2 * ‖m N‖ ≤ ‖m n + m N‖ := by linarith
    have h5 : (2 * ‖m N‖) * (2 * ‖m N‖) ≤ ‖m n + m N‖ * ‖m n + m N‖ :=
      mul_self_le_mul_self (by positivity) h4
    have h6 : ‖m n - m N‖ ^ 2 < ε ^ 2 := by
      nlinarith
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h6
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨p, fun i => ?_⟩
  have hev : ∀ᶠ s in Filter.atTop, m s ∈ Metric.closedBall (y i) (ρ i) := by
    filter_upwards [Filter.eventually_ge_atTop ({i} : Finset I)] with s hs
    have := (hmemC s (m s)).1 (hmC s) i (hs (Finset.mem_singleton_self i))
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have := Metric.isClosed_closedBall.mem_of_tendsto hp hev
  simpa [Metric.mem_closedBall, dist_eq_norm] using this

theorem ose_one_point {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : ℝ) (hL : 0 ≤ L) (G : Set (E × F))
    (hG : ∀ q ∈ G, ∀ q' ∈ G, ‖q.2 - q'.2‖ ≤ L * ‖q.1 - q'.1‖) (z : E) :
    ∃ p : F, ∀ q ∈ G, ‖p - q.2‖ ≤ L * ‖z - q.1‖ := by
  obtain ⟨p, hp⟩ := ose_fip (I := G) (fun q => q.1.2) (fun q => L * ‖z - q.1.1‖) (by
    intro s
    by_cases hs : Nonempty s
    · obtain ⟨p, hp⟩ := ose_kirszbraun_finite (ι := s) L hL (fun i => i.1.1.1) (fun i => i.1.1.2) z
        (fun i j => hG _ i.1.2 _ j.1.2)
      exact ⟨p, fun i hi => hp ⟨i, hi⟩⟩
    · exact ⟨0, fun i hi => (hs ⟨⟨i, hi⟩⟩).elim⟩)
  exact ⟨p, fun q hq => hp ⟨q, hq⟩⟩

theorem ose_kirszbraun {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : ℝ) (hL : 0 ≤ L) (G : Set (E × F))
    (hG : ∀ q ∈ G, ∀ q' ∈ G, ‖q.2 - q'.2‖ ≤ L * ‖q.1 - q'.1‖) :
    ∃ T : E → F, (∀ q ∈ G, T q.1 = q.2) ∧ ∀ u v, ‖T u - T v‖ ≤ L * ‖u - v‖ := by
  classical
  let P : Set (Set (E × F)) := {K | ∀ q ∈ K, ∀ q' ∈ K, ‖q.2 - q'.2‖ ≤ L * ‖q.1 - q'.1‖}
  obtain ⟨K, hGK, hK⟩ := zorn_subset_nonempty P (by
    intro c hcP hchain hne
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    rintro q ⟨s, hs, hq⟩ q' ⟨s', hs', hq'⟩
    rcases hchain.total hs hs' with hss | hss
    · exact hcP hs' _ (hss hq) _ hq'
    · exact hcP hs _ hq _ (hss hq')) G hG
  have hKP : K ∈ P := hK.prop
  have hall : ∀ u : E, ∃ w : F, (u, w) ∈ K := by
    intro u
    obtain ⟨p, hp⟩ := ose_one_point L hL K hKP u
    refine ⟨p, ?_⟩
    have hins : insert (u, p) K ∈ P := by
      rintro q (rfl | hq) q' (rfl | hq')
      · simp
      · simpa using hp q' hq'
      · have := hp q hq
        rw [norm_sub_rev p, norm_sub_rev u] at this
        simpa using this
      · exact hKP _ hq _ hq'
    exact hK.le_of_ge hins (Set.subset_insert _ _) (Set.mem_insert _ _)
  choose T hT using hall
  refine ⟨T, fun q hq => ?_, fun u v => hKP _ (hT u) _ (hT v)⟩
  have := hKP _ (hT q.1) _ (hGK hq)
  simp only [sub_self, norm_zero, mul_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)


theorem ose_extend {X : Type*} [MetricSpace X] {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (A B : Set X) (hAB : ∀ x, x ∈ A ∨ x ∈ B)
    (φ : X → H₁) (hφ : ∀ a ∈ A, ∀ a' ∈ A, dist (φ a) (φ a') = dist a a')
    (ψ : X → H₂) (hψ : ∀ b ∈ B, ∀ b' ∈ B, dist (ψ b) (ψ b') = dist b b')
    (g : X → H₁) (hg : ∀ y, ∀ a ∈ A, dist (g y) (φ a) ≤ dist y a) (hA : A.Nonempty) :
    ∃ F : X → H₁, (∀ a ∈ A, F a = φ a) ∧ ∀ x y, dist (F x) (F y) ≤ 7 * dist x y := by
  classical
  let r : X → ℝ := fun y => Metric.infDist y A
  have hr0 : ∀ y, 0 ≤ r y := fun y => Metric.infDist_nonneg
  have hrA : ∀ y, ∀ a ∈ A, r y ≤ dist y a := fun y a ha => Metric.infDist_le_dist_of_mem ha
  have hrL : ∀ y y', r y ≤ r y' + dist y y' := fun y y' => Metric.infDist_le_infDist_add_dist
  have hgg : ∀ y y', dist (g y) (g y') ≤ dist y y' + 2 * r y := by
    intro y y'
    have : (dist (g y) (g y') - dist y y') / 2 ≤ r y := by
      refine (Metric.le_infDist hA).2 fun a ha => ?_
      have h1 := dist_triangle_right (g y) (g y') (φ a)
      have h2 := hg y a ha
      have h3 := hg y' a ha
      have h4 := dist_triangle y' y a
      rw [dist_comm y' y] at h4
      linarith
    linarith
  obtain ⟨N, -, hN⟩ := zorn_subset_nonempty
    {N : Set X | N ⊆ B ∧ ∀ y ∈ N, ∀ y' ∈ N, y ≠ y' → r y ≤ 2 * dist y y'} (by
      intro c hcP hchain hne
      refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
      · rintro y ⟨s, hs, hy⟩
        exact (hcP hs).1 hy
      · rintro y ⟨s, hs, hy⟩ y' ⟨s', hs', hy'⟩ hne
        rcases hchain.total hs hs' with hss | hss
        · exact (hcP hs').2 _ (hss hy) _ hy' hne
        · exact (hcP hs).2 _ hy _ (hss hy') hne) ∅ ⟨by simp, by simp⟩
  have hNB : N ⊆ B := hN.prop.1
  have hNsep := hN.prop.2
  have hNcov : ∀ y ∈ B, ∃ y0 ∈ N, dist y y0 ≤ r y := by
    intro y hy
    by_cases hyN : y ∈ N
    · exact ⟨y, hyN, by simpa using hr0 y⟩
    · have hnot : ¬ (insert y N ⊆ B ∧
          ∀ u ∈ insert y N, ∀ v ∈ insert y N, u ≠ v → r u ≤ 2 * dist u v) := by
        intro hins
        exact hyN (hN.le_of_ge hins (Set.subset_insert _ _) (Set.mem_insert _ _))
      have hsubB : insert y N ⊆ B := Set.insert_subset hy hNB
      have : ∃ u ∈ insert y N, ∃ v ∈ insert y N, u ≠ v ∧ 2 * dist u v < r u := by
        by_contra hcon
        refine hnot ⟨hsubB, fun u hu v hv huv => ?_⟩
        by_contra hlt
        exact hcon ⟨u, hu, v, hv, huv, not_le.1 hlt⟩
      obtain ⟨u, hu, v, hv, huv, hlt⟩ := this
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact (huv rfl).elim
      · exact ⟨v, hv, by linarith [dist_nonneg (x := u) (y := v)]⟩
      · refine ⟨u, hu, ?_⟩
        have := hrL u v
        rw [dist_comm v u]
        linarith
      · exact absurd hlt (not_lt.2 (hNsep u hu v hv huv))
  let G : Set (H₂ × H₁) := (fun y => (ψ y, g y)) '' N
  have hG : ∀ q ∈ G, ∀ q' ∈ G, ‖q.2 - q'.2‖ ≤ 5 * ‖q.1 - q'.1‖ := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    show ‖g y - g y'‖ ≤ 5 * ‖ψ y - ψ y'‖
    rw [← dist_eq_norm, ← dist_eq_norm, hψ y (hNB hy) y' (hNB hy')]
    by_cases hyy : y = y'
    · subst hyy
      simp
    · have := hNsep y hy y' hy' hyy
      have := hgg y y'
      linarith
  obtain ⟨T, hT, hTL⟩ := ose_kirszbraun 5 (by norm_num) G hG
  have hTN : ∀ y ∈ N, T (ψ y) = g y := fun y hy => hT (ψ y, g y) ⟨y, hy, rfl⟩
  have hTd : ∀ y ∈ B, ∀ y' ∈ B, dist (T (ψ y)) (T (ψ y')) ≤ 5 * dist y y' := by
    intro y hy y' hy'
    rw [dist_eq_norm, ← hψ y hy y' hy', dist_eq_norm]
    exact hTL _ _
  -- the cross estimate
  have hcross : ∀ y ∈ B, ∀ a ∈ A, dist (T (ψ y)) (φ a) ≤ 7 * dist y a := by
    intro y hy a ha
    obtain ⟨y0, hy0, hd⟩ := hNcov y hy
    have h1 := hTd y hy y0 (hNB hy0)
    rw [hTN y0 hy0] at h1
    have h2 := hg y0 a ha
    have h3 := dist_triangle y0 y a
    rw [dist_comm y0 y] at h3
    have h4 := hrA y a ha
    have h5 := dist_triangle (T (ψ y)) (g y0) (φ a)
    linarith
  refine ⟨fun x => if x ∈ A then φ x else T (ψ x), fun a ha => by simp [ha], fun x y => ?_⟩
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
  · simp only [hx, hy, if_true]
    rw [hφ x hx y hy]
    linarith [dist_nonneg (x := x) (y := y)]
  · simp only [hx, hy, if_true, if_false]
    have hyB : y ∈ B := (hAB y).resolve_left hy
    have := hcross y hyB x hx
    rw [dist_comm, dist_comm x y]
    exact this
  · simp only [hx, hy, if_true, if_false]
    exact hcross x ((hAB x).resolve_left hx) y hy
  · simp only [hx, hy, if_false]
    have := hTd x ((hAB x).resolve_left hx) y ((hAB y).resolve_left hy)
    linarith [dist_nonneg (x := x) (y := y)]

theorem ose_euclidean_part {X : Type} [MetricSpace X] (A : Set X)
    (hE : IsOneStronglyEuclidean A) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (φ : X → H), ∀ a ∈ A, ∀ a' ∈ A, dist (φ a) (φ a') = dist a a' := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · exact ⟨ℝ, inferInstance, inferInstance, inferInstance, fun _ => 0, by simp⟩
  · obtain ⟨H, i1, i2, i3, f, hf⟩ := hE a₀
    refine ⟨H, i1, i2, i3, fun x => if h : x ∈ A then f ⟨x, Or.inl h⟩ else 0, ?_⟩
    intro a ha a' ha'
    simp only [ha, ha', dif_pos]
    exact hf.dist_eq _ _

theorem ose_transport {X : Type} [MetricSpace X] {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Set X) (hE : IsOneStronglyEuclidean A)
    (φ : X → H) (hφ : ∀ a ∈ A, ∀ a' ∈ A, dist (φ a) (φ a') = dist a a') (y : X) :
    ∃ p : H, ∀ a ∈ A, dist p (φ a) ≤ dist y a := by
  obtain ⟨K, i1, i2, i3, f, hf⟩ := hE y
  let G : Set (K × H) := (fun a : A => (f ⟨a.1, Or.inl a.2⟩, φ a.1)) '' Set.univ
  obtain ⟨p, hp⟩ := ose_one_point 1 zero_le_one G (by
    rintro _ ⟨a, -, rfl⟩ _ ⟨a', -, rfl⟩
    show ‖φ a.1 - φ a'.1‖ ≤ 1 * ‖f _ - f _‖
    rw [← dist_eq_norm, ← dist_eq_norm, hf.dist_eq, hφ _ a.2 _ a'.2, one_mul]
    rfl) (f ⟨y, Or.inr (Set.mem_singleton y)⟩)
  refine ⟨p, fun a ha => ?_⟩
  have := hp _ ⟨⟨a, ha⟩, trivial, rfl⟩
  simp only [one_mul] at this
  rw [dist_eq_norm]
  refine this.trans (le_of_eq ?_)
  rw [← dist_eq_norm, hf.dist_eq]
  rfl

/-- A union of two 1-strongly Euclidean metric spaces embeds into a Hilbert space with constant distortion. -/
theorem one_strongly_euclidean_union_two_sets_distortion :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type) [MetricSpace X]
        (U : Fin 2 → Set X) (_hU : (⋃ i, U i) = Set.univ)
        (_hE : ∀ i, IsOneStronglyEuclidean (U i)),
        EmbedsIntoHilbertWithDistortion X C := by
  classical
  refine ⟨90, by norm_num, ?_⟩
  intro X _ U hU hE
  have hcov : ∀ x, x ∈ U 0 ∨ x ∈ U 1 := by
    intro x
    have : x ∈ ⋃ i, U i := hU ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 this
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  obtain ⟨H₁, i1, i2, i3, φ, hφ⟩ := ose_euclidean_part (U 0) (hE 0)
  obtain ⟨H₂, j1, j2, j3, ψ, hψ⟩ := ose_euclidean_part (U 1) (hE 1)
  have hext1 : ∃ F : X → H₁, (∀ a ∈ U 0, F a = φ a) ∧ ∀ x y, dist (F x) (F y) ≤ 7 * dist x y := by
    rcases (U 0).eq_empty_or_nonempty with he | hne
    · exact ⟨fun _ => 0, by simp [he], fun x y => by simp [dist_nonneg]⟩
    · choose g hg using ose_transport (U 0) (hE 0) φ hφ
      exact ose_extend (U 0) (U 1) hcov φ hφ ψ hψ g hg hne
  have hext2 : ∃ F : X → H₂, (∀ a ∈ U 1, F a = ψ a) ∧ ∀ x y, dist (F x) (F y) ≤ 7 * dist x y := by
    rcases (U 1).eq_empty_or_nonempty with he | hne
    · exact ⟨fun _ => 0, by simp [he], fun x y => by simp [dist_nonneg]⟩
    · choose g hg using ose_transport (U 1) (hE 1) ψ hψ
      exact ose_extend (U 1) (U 0) (fun x => (hcov x).symm) ψ hψ φ hφ g hg hne
  obtain ⟨F₁, hF₁, hL₁⟩ := hext1
  obtain ⟨F₂, hF₂, hL₂⟩ := hext2
  let D : X → ℝ := fun x => Metric.infDist x (U 1)
  have hD : ∀ x y, |D x - D y| ≤ dist x y := by
    intro x y
    have h1 : D x ≤ D y + dist x y := Metric.infDist_le_infDist_add_dist
    have h2 : D y ≤ D x + dist y x := Metric.infDist_le_infDist_add_dist
    rw [dist_comm y x] at h2
    exact abs_le.2 ⟨by linarith, by linarith⟩
  let E : X → WithLp 2 (WithLp 2 (H₁ × H₂) × ℝ) := fun x =>
    WithLp.toLp 2 (WithLp.toLp 2 (F₁ x, F₂ x), D x)
  have hEsq : ∀ x y, ‖E x - E y‖ ^ 2
      = ‖F₁ x - F₁ y‖ ^ 2 + ‖F₂ x - F₂ y‖ ^ 2 + |D x - D y| ^ 2 := by
    intro x y
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [E, WithLp.prod_norm_sq_eq_of_L2]
    simp
  have hUB : ∀ x y, ‖E x - E y‖ ≤ 10 * dist x y := by
    intro x y
    have h1 := hL₁ x y
    have h2 := hL₂ x y
    have h3 := hD x y
    rw [dist_eq_norm] at h1 h2
    have hd := dist_nonneg (x := x) (y := y)
    have s1 : ‖F₁ x - F₁ y‖ ^ 2 ≤ (7 * dist x y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have s2 : ‖F₂ x - F₂ y‖ ^ 2 ≤ (7 * dist x y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have s3 : |D x - D y| ^ 2 ≤ dist x y ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    have : ‖E x - E y‖ ^ 2 ≤ (10 * dist x y) ^ 2 := by
      rw [hEsq]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 this
  have hc1 : ∀ x y, ‖F₁ x - F₁ y‖ ≤ ‖E x - E y‖ := by
    intro x y
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (two_ne_zero)).1 ?_
    rw [hEsq]
    nlinarith [sq_nonneg ‖F₂ x - F₂ y‖, sq_nonneg |D x - D y|]
  have hc2 : ∀ x y, ‖F₂ x - F₂ y‖ ≤ ‖E x - E y‖ := by
    intro x y
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (two_ne_zero)).1 ?_
    rw [hEsq]
    nlinarith [sq_nonneg ‖F₁ x - F₁ y‖, sq_nonneg |D x - D y|]
  have hc3 : ∀ x y, |D x - D y| ≤ ‖E x - E y‖ := by
    intro x y
    refine (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) (two_ne_zero)).1 ?_
    rw [hEsq]
    nlinarith [sq_nonneg ‖F₁ x - F₁ y‖, sq_nonneg ‖F₂ x - F₂ y‖]
  -- the cross pairs
  have hcross : ∀ x ∈ U 0, ∀ y ∈ U 1, dist x y ≤ 9 * ‖E x - E y‖ := by
    intro x hx y hy
    have hDy : D y = 0 := Metric.infDist_zero_of_mem hy
    have hmain : (dist x y - ‖F₂ x - F₂ y‖) / 8 ≤ D x := by
      refine (Metric.le_infDist ⟨y, hy⟩).2 fun b hb => ?_
      have h1 := dist_triangle x b y
      have h2 : dist b y = dist (F₂ b) (F₂ y) := by
        rw [hF₂ b hb, hF₂ y hy, hψ b hb y hy]
      have h3 := dist_triangle (F₂ b) (F₂ x) (F₂ y)
      have h4 := hL₂ b x
      rw [dist_comm b x] at h4
      rw [dist_eq_norm (F₂ x) (F₂ y)] at h3
      linarith
    have h1 := hc2 x y
    have h2 := hc3 x y
    rw [hDy, sub_zero, abs_of_nonneg Metric.infDist_nonneg] at h2
    linarith
  have hLB : ∀ x y, dist x y ≤ 9 * ‖E x - E y‖ := by
    intro x y
    have hnn := norm_nonneg (E x - E y)
    rcases hcov x with hx | hx <;> rcases hcov y with hy | hy
    · have := hc1 x y
      rw [hF₁ x hx, hF₁ y hy, ← dist_eq_norm, hφ x hx y hy] at this
      linarith
    · exact hcross x hx y hy
    · have := hcross y hy x hx
      rw [dist_comm, norm_sub_rev]
      exact this
    · have := hc2 x y
      rw [hF₂ x hx, hF₂ y hy, ← dist_eq_norm, hψ x hx y hy] at this
      linarith
  refine ⟨WithLp 2 (WithLp 2 (H₁ × H₂) × ℝ), inferInstance, inferInstance, inferInstance,
    fun x => (9 : ℝ) • E x, fun x y => ?_⟩
  have hs : dist ((9 : ℝ) • E x) ((9 : ℝ) • E y) = 9 * ‖E x - E y‖ := by
    rw [dist_eq_norm, ← smul_sub, norm_smul]
    norm_num
  rw [hs]
  exact ⟨hLB x y, by linarith [hUB x y]⟩
