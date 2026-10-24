import AFTD.Prelude
import AFTD.Kb.Tcs.GaleDistanceGraph
import AFTD.Kb.Tcs.GaleSigmaThree
import AFTD.Kb.Tcs.IsGaleCounterexampleThree

/-!
# op462_counterexample_of_integer_witness

Topic: combinatorics   Node: 0c16f8c5dcb6

Provenance: helper lemma. Helper for arXiv:2610.28828, Theorem 2. Reuses the exact coordinate and coloring certificates recorded in experiments 4045 and 4047; convex hull padding is elementary.

An exact integer coordinate certificate and a non-four-colorable witness graph produce a finite counterexample with cardinality at most the number of indexed points.
-/

theorem op462_counterexample_of_integer_witness (n : ℕ) (S Q : ℤ) (hS : 0 < S)
    (P : Fin n → Fin 3 → ℤ) (E : List (Fin n × Fin n))
    (hunit : ∀ i j, (∑ k : Fin 3, (P i k - P j k)^2) ≤ S^2)
    (hedge : E.all (fun e => decide (Q ≤ ∑ k : Fin 3, (P e.1 k - P e.2 k)^2)) = true)
    (hgap : gale_sigma_three^2 < (Q : ℝ) / (S : ℝ)^2)
    (hnotcolor : ∀ c : Fin n → Fin 4, (∀ e ∈ E, c e.1 ≠ c e.2) → False)
    (a b : Fin n) (hab : (a,b) ∈ E) : ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), V.card ≤ n ∧ is_gale_counterexample_three V := by
  classical
  let p : Fin n → EuclideanSpace ℝ (Fin 3) :=
    fun i => WithLp.toLp 2 (fun k => (P i k : ℝ) / (S : ℝ))
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
  have hden : (0 : ℝ) < (S : ℝ)^2 := sq_pos_of_pos hSreal
  have hdistsq (i j : Fin n) :
      dist (p i) (p j)^2 = ((∑ k : Fin 3, (P i k - P j k)^2 : ℤ) : ℝ) / (S : ℝ)^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simp only [p, Real.dist_eq, sq_abs, Int.cast_sum, Int.cast_pow,
      Int.cast_sub, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hdistle (i j : Fin n) : dist (p i) (p j) ≤ 1 := by
    have hh : dist (p i) (p j)^2 ≤ 1 := by
      rw [hdistsq]
      calc
        _ ≤ (S : ℝ)^2 / (S : ℝ)^2 := by
          apply div_le_div_of_nonneg_right _ hden.le
          exact_mod_cast hunit i j
        _ = 1 := div_self hden.ne'
    nlinarith [dist_nonneg (x := p i) (y := p j)]
  have hsig : 0 < gale_sigma_three := by
    unfold gale_sigma_three
    positivity
  have hdistedge (e : Fin n × Fin n) (he : e ∈ E) :
      gale_sigma_three < dist (p e.1) (p e.2) := by
    have he' := (List.all_eq_true.mp hedge) e he
    have hi : Q ≤ ∑ k : Fin 3, (P e.1 k - P e.2 k)^2 := of_decide_eq_true he'
    have hh : (Q : ℝ) / (S : ℝ)^2 ≤ dist (p e.1) (p e.2)^2 := by
      rw [hdistsq]
      apply div_le_div_of_nonneg_right _ hden.le
      exact_mod_cast hi
    nlinarith [dist_nonneg (x := p e.1) (y := p e.2)]
  let V : Finset (EuclideanSpace ℝ (Fin 3)) := Finset.univ.image p
  have hp (i : Fin n) : p i ∈ (V : Set (EuclideanSpace ℝ (Fin 3))) := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hdiamle : Metric.diam (V : Set (EuclideanSpace ℝ (Fin 3))) ≤ 1 := by
    apply Metric.diam_le_of_forall_dist_le (by norm_num)
    intro x hx y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact hdistle i j
  have hdiampos : 0 < Metric.diam (V : Set (EuclideanSpace ℝ (Fin 3))) := by
    apply lt_of_lt_of_le (hsig.trans (hdistedge (a,b) hab))
    exact Metric.dist_le_diam_of_mem V.finite_toSet.isBounded (hp a) (hp b)
  have hV : is_gale_counterexample_three V := by
    refine ⟨hdiampos, ?_⟩
    rintro ⟨c⟩
    apply hnotcolor (fun i => c ⟨p i, hp i⟩)
    intro e he
    apply c.valid
    have hed := hdistedge e he
    have hne : p e.1 ≠ p e.2 := dist_pos.mp (hsig.trans hed)
    change (⟨p e.1, hp e.1⟩ : V) ≠ ⟨p e.2, hp e.2⟩ ∧
      gale_sigma_three * Metric.diam (V : Set (EuclideanSpace ℝ (Fin 3))) < dist (p e.1) (p e.2)
    constructor
    · exact fun hh => hne (congrArg Subtype.val hh)
    · exact lt_of_le_of_lt (mul_le_of_le_one_right hsig.le hdiamle) hed
  exact ⟨V, Finset.card_image_le.trans_eq (by simp), hV⟩
