import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetMidpointBalancedCardGeThree
import AFTD.Kb.Tcs.FinsetExistsMinimalMidpointBalanced
import AFTD.Kb.Tcs.DiscreteMaxPrincipleStep
import AFTD.Kb.Tcs.FinsetImageBalancedOfClosed
import AFTD.Kb.Tcs.FinsetIsMidpointBalanced
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# finset_midpoint_balanced_exists_nonzero_minor

Topic: combinatorics   Node: f7aeaee2ebea

Provenance: helper lemma. step towards finset_card_ge_one_add_clog_of_midpoint_balanced

Every nonempty midpoint-balanced subset B of ZMod p contains an inclusion-minimal balanced subconfiguration of size k+1 ≤ |B| with k > 0 whose certificate matrix has at least one non-vanishing minor.
-/

lemma finset_midpoint_balanced_exists_nonzero_minor_mulVec_zero_harmonic (k : ℕ)
    (u v : Fin (k + 1) → Fin (k + 1)) (w : Fin k → ℤ)
    (hM : Matrix.mulVec ((Matrix.of fun (i j : Fin (k + 1)) =>
      (if j = i then (2 : ℤ) else 0) - (if j = u i then 1 else 0) - (if j = v i then 1 else 0)).submatrix
      (0 : Fin (k + 1)).succAbove (0 : Fin (k + 1)).succAbove) w = 0) :
    let w_ext : Fin (k + 1) → ℤ := Fin.cons 0 w
    ∀ l : Fin k, 2 * w_ext l.succ = w_ext (u l.succ) + w_ext (v l.succ) := by
  intro w_ext l
  have hl := congr_fun hM l
  dsimp [Matrix.mulVec, dotProduct] at hl
  let f : Fin (k + 1) → ℤ := fun j =>
    ((if j = l.succ then (2 : ℤ) else 0) -
     (if j = u l.succ then 1 else 0) -
     (if j = v l.succ then 1 else 0)) * w_ext j
  have hsplit : ∑ j : Fin (k + 1), f j = 0 := by
    rw [Fin.sum_univ_succ f]
    have h0 : f 0 = 0 := by
      dsimp [f, w_ext]
      rw [Fin.cons_zero, mul_zero]
    rw [h0, zero_add]
    have heq : (∑ m : Fin k, f m.succ) = ∑ m : Fin k,
      (((if m.succ = l.succ then (2 : ℤ) else 0) -
        (if m.succ = u l.succ then 1 else 0) -
        (if m.succ = v l.succ then 1 else 0)) * w m) := by
      apply Finset.sum_congr rfl
      intro m _
      dsimp [f, w_ext]
      rw [Fin.cons_succ]
    rw [heq, hl]
  have hsum : ∑ j : Fin (k + 1), f j = 2 * w_ext l.succ - w_ext (u l.succ) - w_ext (v l.succ) := by
    have h1 : ∀ j : Fin (k + 1), f j =
      (if j = l.succ then 2 * w_ext j else 0) -
      (if j = u l.succ then w_ext j else 0) -
      (if j = v l.succ then w_ext j else 0) := by
      intro j
      dsimp [f]
      split_ifs <;> ring
    simp_rw [h1, sub_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq']
  linarith [hsplit, hsum]

lemma finset_midpoint_balanced_exists_nonzero_minor_pos_harmonic (k : ℕ)
    (u v : Fin (k + 1) → Fin (k + 1)) (w : Fin k → ℤ) (hw : w ≠ 0)
    (h_harm : ∀ l : Fin k, 2 * (Fin.cons 0 w : Fin (k + 1) → ℤ) l.succ =
      (Fin.cons 0 w : Fin (k + 1) → ℤ) (u l.succ) + (Fin.cons 0 w : Fin (k + 1) → ℤ) (v l.succ)) :
    ∃ (w' : Fin (k + 1) → ℤ),
      w' 0 = 0 ∧
      (∀ l : Fin k, 2 * w' l.succ = w' (u l.succ) + w' (v l.succ)) ∧
      ∃ j : Fin (k + 1), 0 < w' j := by
  have hw_ex : ∃ l : Fin k, w l ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  obtain ⟨l, hl⟩ := hw_ex
  let w_ext : Fin (k + 1) → ℤ := Fin.cons 0 w
  have hl_ext : w_ext l.succ ≠ 0 := by
    dsimp [w_ext]
    rw [Fin.cons_succ]
    exact hl
  rcases lt_or_gt_of_ne hl_ext with hneg | hpos
  · refine ⟨-w_ext, ?_, ?_, l.succ, ?_⟩
    · simp [w_ext]
    · intro l'
      dsimp
      linarith [h_harm l']
    · dsimp
      linarith
  · refine ⟨w_ext, ?_, h_harm, l.succ, hpos⟩
    simp [w_ext]

/-- Every nonempty midpoint-balanced subset B of ZMod p contains a subconfiguration with a non-zero minor. -/
theorem finset_midpoint_balanced_exists_nonzero_minor {p : ℕ} [Fact p.Prime]
    (B : Finset (ZMod p)) (hB : finset_is_midpoint_balanced B) :
    ∃ (k : ℕ) (hk0 : 0 < k) (hk : k + 1 ≤ B.card) (u v : Fin (k + 1) → Fin (k + 1))
      (b : Fin (k + 1) → ZMod p) (hinj : Function.Injective b)
      (hmid : ∀ i, 2 * b i = b (u i) + b (v i))
      (i₀ j₀ : Fin (k + 1)),
      ((Matrix.of fun (i j : Fin (k + 1)) =>
        (if j = i then (2 : ℤ) else 0) - (if j = u i then 1 else 0) - (if j = v i then 1 else 0)).submatrix
        i₀.succAbove j₀.succAbove).det ≠ 0 := by
  obtain ⟨B₀, hB₀B, hB₀bal, hB₀min⟩ := finset_exists_minimal_midpoint_balanced B hB
  have _hcard3 := finset_midpoint_balanced_card_ge_three B₀ hB₀bal
  let k := B₀.card - 1
  have hk0 : 0 < k := by dsimp [k]; omega
  have hkeq : k + 1 = B₀.card := by dsimp [k]; omega
  have hkB : k + 1 ≤ B.card := by
    rw [hkeq]
    exact Finset.card_le_card hB₀B
  have e1 : Fin (k + 1) ≃ Fin B₀.card := (finCongr hkeq.symm).symm
  have e2 : Fin B₀.card ≃ ↥B₀ := (Finset.equivFin B₀).symm
  let e : Fin (k + 1) ≃ ↥B₀ := e1.trans e2
  let b : Fin (k + 1) → ZMod p := fun i => (e i : ZMod p)
  have hinj : Function.Injective b := by
    intro x y hxy
    have : e x = e y := Subtype.ext hxy
    exact e.injective this
  have h_range : Finset.univ.image b = B₀ := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro ha
      have : (⟨a, ha⟩ : ↥B₀) ∈ Set.range e := e.surjective.range_eq ▸ Set.mem_univ _
      obtain ⟨i, hi⟩ := this
      refine ⟨i, ?_⟩
      dsimp [b]
      rw [hi]
  have h_each : ∀ i : Fin (k + 1), ∃ (ui vi : Fin (k + 1)),
      ui ≠ i ∧ vi ≠ i ∧ ui ≠ vi ∧ 2 * b i = b ui + b vi ∧ b i + b i = b ui + b vi := by
    intro i
    have hbi : b i ∈ B₀ := by
      rw [← h_range]
      exact Finset.mem_image_of_mem b (Finset.mem_univ i)
    obtain ⟨u', hu', v', hv', hune, hvne, huvne, hmid'⟩ := hB₀bal.2 (b i) hbi
    rw [← h_range, Finset.mem_image] at hu' hv'
    obtain ⟨ui, _, rfl⟩ := hu'
    obtain ⟨vi, _, rfl⟩ := hv'
    have hui : ui ≠ i := fun h => hune (by rw [h])
    have hvi : vi ≠ i := fun h => hvne (by rw [h])
    have huvi : ui ≠ vi := fun h => huvne (by rw [h])
    have h2 : 2 * b i = b ui + b vi := by
      rw [two_mul, hmid']
    exact ⟨ui, vi, hui, hvi, huvi, h2, hmid'⟩
  choose u v hu hv huv hmid hmid_add using h_each
  refine ⟨k, hk0, hkB, u, v, b, hinj, hmid, 0, 0, ?_⟩
  let M := (Matrix.of fun (i j : Fin (k + 1)) =>
    (if j = i then (2 : ℤ) else 0) - (if j = u i then 1 else 0) - (if j = v i then 1 else 0)).submatrix
    (0 : Fin (k + 1)).succAbove (0 : Fin (k + 1)).succAbove
  intro hdet
  have h_kernel := (@Matrix.exists_mulVec_eq_zero_iff (Fin k) _ ℤ _ _ M _).symm.mp hdet
  obtain ⟨w, hw_ne, hw_mul⟩ := h_kernel
  have h_harm := finset_midpoint_balanced_exists_nonzero_minor_mulVec_zero_harmonic k u v w hw_mul
  obtain ⟨w', hw'0, hw'_harm, j, hjpos⟩ := finset_midpoint_balanced_exists_nonzero_minor_pos_harmonic k u v w hw_ne h_harm
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ w' Finset.univ_nonempty
  have hV : 0 < w' m := lt_of_lt_of_le hjpos (hm j (Finset.mem_univ j))
  have hmax : ∀ j, w' j ≤ w' m := fun j => hm j (Finset.mem_univ j)
  have hstep := discrete_max_principle_step k u v w' hw'0 hw'_harm (w' m) hV m rfl hmax
  rcases hstep with ⟨hSne, h0notinS, hS_closed⟩
  let S := Finset.univ.filter (fun j => w' j = w' m)
  have hS_bal : finset_is_midpoint_balanced (S.image b) :=
    finset_image_balanced_of_closed b hinj u v hu hv huv hmid_add S hSne hS_closed
  have h_sub : S.image b ⊆ B₀ := by
    rw [← h_range]
    exact Finset.image_subset_image (Finset.subset_univ S)
  have heq : S.image b = B₀ := hB₀min (S.image b) h_sub hS_bal
  have hb0_in : b 0 ∈ B₀ := by
    rw [← h_range]
    exact Finset.mem_image_of_mem b (Finset.mem_univ 0)
  rw [← heq, Finset.mem_image] at hb0_in
  obtain ⟨j₀, hj₀, hj₀0⟩ := hb0_in
  have : j₀ = 0 := hinj hj₀0
  exact h0notinS (this ▸ hj₀)
