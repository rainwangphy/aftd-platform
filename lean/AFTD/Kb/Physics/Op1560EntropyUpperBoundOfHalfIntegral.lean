import AFTD.Prelude
import AFTD.Kb.Physics.CubicStationaryEntropyInf
import AFTD.Kb.Physics.CubicEdgeEntropy
import AFTD.Kb.Physics.IsHalfIntegralCurrent
import AFTD.Kb.Physics.IsStationaryCurrent
import AFTD.Kb.Physics.SimpleGraphOrientation

/-!
# op_1560_entropy_upper_bound_of_half_integral

Topic: statistical_mechanics   Node: af73ba3fa7a0

Provenance: helper lemma. arXiv:2204.00875

For any finite simple graph G with orientation o and any half-integral stationary current j on G.edgeFinset with sum of |j(e)| equal to the number of vertices n, and any 0 < J < n, the infimal stationary entropy production S_G(J) is at most the number of edges with |j(e)| = 1 times phi(J/n) plus the number of edges with |j(e)| = 1/2 times phi(J/(2n)).
-/

private lemma op_1560_entropy_upper_bound_of_half_integral_neg (x : ℝ) :
    cubic_edge_entropy (-x) = cubic_edge_entropy x := by
  simp [cubic_edge_entropy, abs_neg]

private lemma op_1560_entropy_upper_bound_of_half_integral_nonneg {x : ℝ} (hx : |x| < 1) :
    0 ≤ cubic_edge_entropy x := by
  unfold cubic_edge_entropy
  apply mul_nonneg (abs_nonneg x)
  apply Real.log_nonneg
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - |x|)]
  have := abs_nonneg x
  linarith

private lemma op_1560_entropy_upper_bound_of_half_integral_edge_scale {t : ℝ} (_ht0 : 0 < t) (x : ℝ)
    (hx : x = 0 ∨ x = 1/2 ∨ x = -1/2 ∨ x = 1 ∨ x = -1) :
    cubic_edge_entropy (t * x) =
      (if |x| = 1 then (1:ℝ) else 0) * cubic_edge_entropy t +
      (if |x| = 1/2 then (1:ℝ) else 0) * cubic_edge_entropy (t/2) := by
  rcases hx with h|h|h|h|h
  · subst h; simp [cubic_edge_entropy]
  · subst h
    have h1 : cubic_edge_entropy (t * (1/2:ℝ)) = cubic_edge_entropy (t/2) := by congr 1; ring
    rw [h1]; norm_num
  · subst h
    have h1 : cubic_edge_entropy (t * (-1/2:ℝ)) = cubic_edge_entropy (t/2) := by
      have hh : t * (-1/2:ℝ) = -(t/2) := by ring
      rw [hh, op_1560_entropy_upper_bound_of_half_integral_neg]
    rw [h1]; norm_num
  · subst h; simp [cubic_edge_entropy]
  · subst h
    have h1 : cubic_edge_entropy (t * (-1:ℝ)) = cubic_edge_entropy t := by
      have hh : t * (-1:ℝ) = -t := by ring
      rw [hh, op_1560_entropy_upper_bound_of_half_integral_neg]
    rw [h1]; norm_num

/-- Scaling a half-integral stationary current provides an explicit upper bound on the continuous entropy infimum. -/
theorem op_1560_entropy_upper_bound_of_half_integral
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (o : SimpleGraphOrientation G)
    (j : G.edgeFinset → ℝ)
    (hj_stat : is_stationary_current G o j)
    (hj_half : is_half_integral_current G j)
    (hj_sum : ∑ e : G.edgeFinset, |j e| = Fintype.card V)
    (J : ℝ) (hJ_pos : 0 < J) (hJ_lt : J < Fintype.card V) :
    cubic_stationary_entropy_inf G o J ≤
      (∑ e : G.edgeFinset, if |j e| = 1 then (1 : ℝ) else 0) *
        cubic_edge_entropy (J / Fintype.card V) +
      (∑ e : G.edgeFinset, if |j e| = 1/2 then (1 : ℝ) else 0) *
        cubic_edge_entropy (J / (2 * Fintype.card V)) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hn_pos : 0 < n := by
    rw [hn_def]
    by_contra h
    have : (Fintype.card V : ℝ) ≤ 0 := le_of_not_gt h
    linarith
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  set t : ℝ := J / n with ht_def
  have ht_pos : 0 < t := by rw [ht_def]; exact div_pos hJ_pos hn_pos
  have ht_lt : t < 1 := by
    rw [ht_def, div_lt_one hn_pos]
    simpa using hJ_lt
  let j' : G.edgeFinset → ℝ := fun e => t * j e
  have hstat : is_stationary_current G o j' := by
    intro v
    have hv := hj_stat v
    have hterm : ∀ e : ↥G.edgeFinset,
        ((if (o.dir e).1 = v then j' e else 0) - if (o.dir e).2 = v then j' e else 0)
        = t * ((if (o.dir e).1 = v then j e else 0) - if (o.dir e).2 = v then j e else 0) := by
      intro e
      by_cases h1 : (o.dir e).1 = v <;> by_cases h2 : (o.dir e).2 = v <;>
        simp [j', h1, h2]
    calc ∑ e, ((if (o.dir e).1 = v then j' e else 0) - if (o.dir e).2 = v then j' e else 0)
        = ∑ e, t * ((if (o.dir e).1 = v then j e else 0) - if (o.dir e).2 = v then j e else 0) :=
          Finset.sum_congr rfl (fun e _ => hterm e)
      _ = t * ∑ e, ((if (o.dir e).1 = v then j e else 0) - if (o.dir e).2 = v then j e else 0) := by
          rw [Finset.mul_sum]
      _ = t * 0 := by rw [hv]
      _ = 0 := by ring
  have hbound : ∀ e : G.edgeFinset, |j' e| < 1 := by
    intro e
    have he := hj_half e
    have habs : |j e| ≤ 1 := by
      rcases he with h|h|h|h|h <;> rw [h] <;> norm_num
    have h1 : |j' e| = t * |j e| := by
      simp [j', abs_mul, abs_of_pos ht_pos]
    rw [h1]
    calc t * |j e| ≤ t * 1 := mul_le_mul_of_nonneg_left habs (le_of_lt ht_pos)
      _ = t := by ring
      _ < 1 := ht_lt
  have hsum : ∑ e : G.edgeFinset, |j' e| = J := by
    have h1 : ∑ e : G.edgeFinset, |j' e| = ∑ e : G.edgeFinset, t * |j e| := by
      apply Finset.sum_congr rfl; intro e _; simp [j', abs_mul, abs_of_pos ht_pos]
    rw [h1, ← Finset.mul_sum, hj_sum]
    rw [ht_def, div_mul_cancel₀ J hn_ne]
  have hentropy_t : ∑ e : G.edgeFinset, cubic_edge_entropy (j' e) =
      (∑ e : G.edgeFinset, if |j e| = 1 then (1:ℝ) else 0) * cubic_edge_entropy t +
      (∑ e : G.edgeFinset, if |j e| = 1/2 then (1:ℝ) else 0) * cubic_edge_entropy (t/2) := by
    have hper : ∀ e ∈ (Finset.univ : Finset ↥G.edgeFinset), cubic_edge_entropy (j' e) =
        (if |j e| = 1 then (1:ℝ) else 0) * cubic_edge_entropy t +
        (if |j e| = 1/2 then (1:ℝ) else 0) * cubic_edge_entropy (t/2) := by
      intro e _
      exact op_1560_entropy_upper_bound_of_half_integral_edge_scale ht_pos (j e) (hj_half e)
    calc ∑ e : G.edgeFinset, cubic_edge_entropy (j' e)
        = ∑ e : G.edgeFinset, ((if |j e| = 1 then (1:ℝ) else 0) * cubic_edge_entropy t +
            (if |j e| = 1/2 then (1:ℝ) else 0) * cubic_edge_entropy (t/2)) :=
          Finset.sum_congr rfl hper
      _ = (∑ e : G.edgeFinset, (if |j e| = 1 then (1:ℝ) else 0) * cubic_edge_entropy t) +
            (∑ e : G.edgeFinset, (if |j e| = 1/2 then (1:ℝ) else 0) * cubic_edge_entropy (t/2)) :=
          Finset.sum_add_distrib
      _ = (∑ e : G.edgeFinset, if |j e| = 1 then (1:ℝ) else 0) * cubic_edge_entropy t +
            (∑ e : G.edgeFinset, if |j e| = 1/2 then (1:ℝ) else 0) * cubic_edge_entropy (t/2) := by
          rw [Finset.sum_mul, Finset.sum_mul]
  have hentropy : ∑ e : G.edgeFinset, cubic_edge_entropy (j' e) =
      (∑ e : G.edgeFinset, if |j e| = 1 then (1:ℝ) else 0) * cubic_edge_entropy (J / n) +
      (∑ e : G.edgeFinset, if |j e| = 1/2 then (1:ℝ) else 0) * cubic_edge_entropy (J / (2 * n)) := by
    rw [hentropy_t]
    have ht2 : t / 2 = J / (2 * n) := by rw [ht_def]; field_simp
    rw [ht2, ht_def]
  have hbdd : BddBelow {s : ℝ | ∃ jj : ↥G.edgeFinset → ℝ,
      is_stationary_current G o jj ∧ (∀ e, |jj e| < 1) ∧ ∑ e, |jj e| = J ∧
      ∑ e, cubic_edge_entropy (jj e) = s} := by
    refine ⟨0, ?_⟩
    rintro s ⟨jj, _, h1, _, rfl⟩
    exact Finset.sum_nonneg (fun e _ => op_1560_entropy_upper_bound_of_half_integral_nonneg (h1 e))
  have hmem : (∑ e : G.edgeFinset, cubic_edge_entropy (j' e)) ∈
      {s : ℝ | ∃ jj : ↥G.edgeFinset → ℝ,
        is_stationary_current G o jj ∧ (∀ e, |jj e| < 1) ∧ ∑ e, |jj e| = J ∧
        ∑ e, cubic_edge_entropy (jj e) = s} :=
    ⟨j', hstat, hbound, hsum, rfl⟩
  rw [cubic_stationary_entropy_inf]
  exact le_trans (csInf_le hbdd hmem) (le_of_eq hentropy)
