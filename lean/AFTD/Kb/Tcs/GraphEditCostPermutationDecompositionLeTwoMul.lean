import AFTD.Prelude
import AFTD.Kb.Tcs.GraphEditCost
import AFTD.Kb.Tcs.PermEditCost
import AFTD.Kb.Tcs.PermEditCostEqGraphEditCost
import AFTD.Kb.Tcs.IsDoublyStochastic
import AFTD.Kb.Tcs.G

/-!
# graph_edit_cost_permutation_decomposition_le_two_mul

Topic: graphs   Node: b69ce7517faa

Provenance: formalization of a published result. Source: arXiv:2611.05048 Theorem 6

Let $Q$ be an $n \times n$ doubly stochastic matrix with a convex decomposition $Q = \sum_{i \in \iota} w_i P_{\pi_i}$, where $w_i \ge 0$, $\sum_{i} w_i = 1$, and each $\pi_i$ is a permutation of $\{0, \dots, n-1\}$. Then for any binary matrices $A, B \in \{0, 1\}^{n \times n}$, the weighted sum of permutation edit costs satisfies $\sum_{i \in \iota} w_i \mathcal{C}_{\mathsf{ed}}(\pi_i) \le 2 \mathcal{C}_{\mathsf{ed}}(Q)$.
-/

open Matrix Finset
set_option maxHeartbeats 4000000

/-- Evaluation map from matrices (as functions on products) to Euclidean space. -/
def gedToE (n : ℕ) : (Fin n × Fin n → ℝ) → EuclideanSpace ℝ (Fin n × Fin n) :=
  (WithLp.equiv 2 (Fin n × Fin n → ℝ)).symm

/-- Move the two outer sums of a fourfold sum to the innermost position. -/
lemma ged_sw4 {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    (f : a → b → c → d → ℝ) :
    (∑ x, ∑ y, ∑ z, ∑ t, f x y z t) = ∑ z, ∑ t, ∑ x, ∑ y, f x y z t := by
  have h := Finset.sum_comm (s := (Finset.univ : Finset (a × b)))
    (t := (Finset.univ : Finset (c × d))) (f := fun p q => f p.1 p.2 q.1 q.2)
  calc ∑ x, ∑ y, ∑ z, ∑ t, f x y z t
      = ∑ p : a × b, ∑ q : c × d, f p.1 p.2 q.1 q.2 := by simp [Fintype.sum_prod_type]
    _ = ∑ q : c × d, ∑ p : a × b, f p.1 p.2 q.1 q.2 := h
    _ = ∑ z, ∑ t, ∑ x, ∑ y, f x y z t := by simp [Fintype.sum_prod_type]

/-- Summation against a Kronecker delta picks out one term. -/
lemma ged_delta {n : ℕ} (f : Fin n → Fin n → ℝ) (d e : Fin n) :
    ∑ w, ∑ w', f w w' * (if d = w then (1:ℝ) else 0) * (if e = w' then (1:ℝ) else 0) = f d e := by
  have h1 : ∀ w, (∑ w', f w w' * (if d = w then (1:ℝ) else 0) * (if e = w' then (1:ℝ) else 0))
      = f w e * (if d = w then (1:ℝ) else 0) := by
    intro w
    rw [Finset.sum_eq_single e]
    · simp
    · intro b _ hb; simp only [if_neg (Ne.symm hb), mul_zero]
    · intro h; exact absurd (Finset.mem_univ e) h
  simp only [h1]
  rw [Finset.sum_eq_single d]
  · rw [if_pos rfl, mul_one]
  · intro b _ hb; simp only [if_neg (Ne.symm hb), mul_zero]
  · intro h; exact absurd (Finset.mem_univ d) h

/-- Distribute a convex combination across a doubly weighted sum. -/
lemma ged_block {n : ℕ} {ι : Type*} [Fintype ι] (G : Fin n → Fin n → ℝ)
    (w : ι → ℝ) (d1 d2 : ι → Fin n) :
    ∑ ww, ∑ ww', G ww ww' * (∑ i, w i * (if d1 i = ww then (1:ℝ) else 0))
       * (∑ j, w j * (if d2 j = ww' then (1:ℝ) else 0))
      = ∑ i, ∑ j, w i * w j * G (d1 i) (d2 j) := by
  have key : ∀ ww ww', G ww ww' * (∑ i, w i * (if d1 i = ww then (1:ℝ) else 0))
       * (∑ j, w j * (if d2 j = ww' then (1:ℝ) else 0))
      = ∑ i, ∑ j, G ww ww' * ((w i * (if d1 i = ww then (1:ℝ) else 0))
          * (w j * (if d2 j = ww' then (1:ℝ) else 0))) := by
    intro ww ww'
    have hAB := Finset.sum_mul_sum (s := (univ : Finset ι)) (t := (univ : Finset ι))
      (f := fun i => w i * (if d1 i = ww then (1:ℝ) else 0))
      (g := fun j => w j * (if d2 j = ww' then (1:ℝ) else 0))
    calc G ww ww' * (∑ i, w i * (if d1 i = ww then (1:ℝ) else 0))
          * (∑ j, w j * (if d2 j = ww' then (1:ℝ) else 0))
        = G ww ww' * ((∑ i, w i * (if d1 i = ww then (1:ℝ) else 0))
          * (∑ j, w j * (if d2 j = ww' then (1:ℝ) else 0))) := by ring
      _ = G ww ww' * (∑ i, ∑ j, (w i * (if d1 i = ww then (1:ℝ) else 0))
            * (w j * (if d2 j = ww' then (1:ℝ) else 0))) := by rw [hAB]
      _ = ∑ i, G ww ww' * (∑ j, (w i * (if d1 i = ww then (1:ℝ) else 0))
            * (w j * (if d2 j = ww' then (1:ℝ) else 0))) := by rw [Finset.mul_sum]
      _ = ∑ i, ∑ j, G ww ww' * ((w i * (if d1 i = ww then (1:ℝ) else 0))
            * (w j * (if d2 j = ww' then (1:ℝ) else 0))) := by
        apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
  simp only [key]
  rw [ged_sw4 (fun ww ww' i j => G ww ww' * ((w i * (if d1 i = ww then (1:ℝ) else 0))
          * (w j * (if d2 j = ww' then (1:ℝ) else 0))))]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [show (∑ x, ∑ x_1, G x x_1 * ((w i * (if d1 i = x then (1:ℝ) else 0))
          * (w j * (if d2 j = x_1 then (1:ℝ) else 0))))
        = ∑ x, ∑ x_1, ((w i * w j) * G x x_1) * (if d1 i = x then (1:ℝ) else 0)
          * (if d2 j = x_1 then (1:ℝ) else 0) from by
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    ring]
  rw [ged_delta (fun a b => (w i * w j) * G a b) (d1 i) (d2 j)]

/-- Entries of the convex combination of permutation matrices. -/
lemma ged_Q_entry {n : ℕ} {ι : Type*} [Fintype ι] (Q : Matrix (Fin n) (Fin n) ℝ)
    (w : ι → ℝ) (π : ι → Equiv.Perm (Fin n))
    (hQ : ∑ i, w i • (π i).permMatrix ℝ = Q) :
    ∀ v ww, Q v ww = ∑ i, w i * (if (π i) v = ww then (1:ℝ) else 0) := by
  intro v ww
  have hP : ∀ (i : ι) (a b : Fin n), ((π i).permMatrix ℝ) a b = if (π i) a = b then (1:ℝ) else 0 :=
    fun i a b => by simp [Equiv.Perm.permMatrix, Equiv.toPEquiv]
  have hthis : ∑ x, w x * ((π x).permMatrix ℝ) v ww = Q v ww := by
    have := congrFun (congrFun hQ v) ww
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using this
  rw [← hthis]
  apply Finset.sum_congr rfl; intro i _
  rw [hP]

/-- Absolute values of differences of binary entries are squares. -/
lemma ged_abs_sq {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (hB : ∀ i j, B i j = 0 ∨ B i j = 1) :
    ∀ v v' w w', |A v v' - B w w'| = (A v v' - B w w') ^ 2 := by
  intro v v' w w'
  rcases hA v v' with h | h <;> rcases hB w w' with g | g <;> rw [h, g] <;> norm_num

/-- The graph edit cost as a sum of squares. -/
lemma ged_graph_eq_sq {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (hB : ∀ i j, B i j = 0 ∨ B i j = 1)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    graph_edit_cost A B Q
      = ∑ v, ∑ v', ∑ w, ∑ w', (A v v' - B w w') ^ 2 * Q v w * Q v' w' := by
  rw [graph_edit_cost]
  apply Finset.sum_congr rfl; intro v _
  apply Finset.sum_congr rfl; intro v' _
  apply Finset.sum_congr rfl; intro w _
  apply Finset.sum_congr rfl; intro w' _
  rw [ged_abs_sq A B hA hB]

/-- The permutation edit cost as a sum of squares. -/
lemma ged_perm_cost_eq {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (hB : ∀ i j, B i j = 0 ∨ B i j = 1)
    (π : Equiv.Perm (Fin n)) :
    perm_edit_cost A B π = ∑ v, ∑ v', (A v v' - B (π v) (π v')) ^ 2 := by
  rw [perm_edit_cost]
  apply Finset.sum_congr rfl; intro v _
  apply Finset.sum_congr rfl; intro v' _
  rw [ged_abs_sq A B hA hB]

/-- Squared distance between the two vector families, in permutation-cost form. -/
lemma ged_norm_pair {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (σ τ : Equiv.Perm (Fin n)) :
    ‖gedToE n (fun p : Fin n × Fin n => A (σ.symm p.1) p.2)
      - gedToE n (fun p : Fin n × Fin n => B p.1 (τ p.2))‖ ^ 2
      = ∑ u, ∑ v', (A u v' - B (σ u) (τ v')) ^ 2 := by
  have h1 : ∀ p : Fin n × Fin n,
      (gedToE n (fun p : Fin n × Fin n => A (σ.symm p.1) p.2)
        - gedToE n (fun p : Fin n × Fin n => B p.1 (τ p.2))) p
      = A (σ.symm p.1) p.2 - B p.1 (τ p.2) := by
    intro p; simp [gedToE, WithLp.equiv]
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  simp only [h1]
  rw [← Equiv.sum_comp σ.symm (fun a => ∑ v', (A a v' - B (σ a) (τ v')) ^ 2)]
  apply Finset.sum_congr rfl; intro v _
  apply Finset.sum_congr rfl; intro v' _
  simp

/-- Abstract Hilbert-space inequality: a weighted average of squared distances to the
matched points is at most twice the weighted average of all pairwise squared distances. -/
lemma ged_abstract_ineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∑ i, w i = 1) (hw_nn : ∀ i, 0 ≤ w i)
    (α q : ι → E) :
    ∑ i, w i * ‖α i - q i‖ ^ 2 ≤ 2 * (∑ i, ∑ j, w i * w j * ‖α i - q j‖ ^ 2) := by
  set S := ∑ i, w i • α i with hS
  set T := ∑ i, w i • q i with hT
  have hST : ∑ i, w i * inner ℝ (α i) T = inner ℝ S T := by
    rw [hS, sum_inner]; apply Finset.sum_congr rfl; intro i _; rw [real_inner_smul_left]
  have hST2 : ∑ i, w i * inner ℝ S (q i) = inner ℝ S T := by
    rw [hT, inner_sum]; apply Finset.sum_congr rfl; intro i _; rw [real_inner_smul_right]
  have hSS' : ∑ i, w i * inner ℝ S (α i) = inner ℝ S S := by
    rw [hS, inner_sum]; apply Finset.sum_congr rfl; intro i _; rw [real_inner_smul_right]
  have hSS : ∑ i, w i * inner ℝ (α i) S = ‖S‖ ^ 2 := by
    have e : ∑ i, w i * inner ℝ (α i) S = ∑ i, w i * inner ℝ S (α i) := by
      apply Finset.sum_congr rfl; intro i _; rw [real_inner_comm]
    rw [e, hSS', real_inner_self_eq_norm_sq]
  have hTT' : ∑ i, w i * inner ℝ T (q i) = inner ℝ T T := by
    rw [hT, inner_sum]; apply Finset.sum_congr rfl; intro i _; rw [real_inner_smul_right]
  have hTT : ∑ i, w i * inner ℝ (q i) T = ‖T‖ ^ 2 := by
    have e : ∑ i, w i * inner ℝ (q i) T = ∑ i, w i * inner ℝ T (q i) := by
      apply Finset.sum_congr rfl; intro i _; rw [real_inner_comm]
    rw [e, hTT', real_inner_self_eq_norm_sq]
  have h1 : ∑ i, w i * ‖α i - S‖ ^ 2 = ∑ i, w i * ‖α i‖ ^ 2 - ‖S‖ ^ 2 := by
    have k : ∀ i, w i * ‖α i - S‖ ^ 2
        = w i * ‖α i‖ ^ 2 - 2 * (w i * inner ℝ (α i) S) + w i * ‖S‖ ^ 2 := by
      intro i; rw [norm_sub_sq_real]; ring
    simp only [k, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hh1 : ∑ i, 2 * (w i * inner ℝ (α i) S) = 2 * ‖S‖ ^ 2 := by
      rw [← Finset.mul_sum, hSS]
    have hh2 : ∑ i, w i * ‖S‖ ^ 2 = ‖S‖ ^ 2 := by rw [← Finset.sum_mul, hw, one_mul]
    rw [hh1, hh2]; ring
  have h2 : ∑ i, w i * ‖q i - T‖ ^ 2 = ∑ i, w i * ‖q i‖ ^ 2 - ‖T‖ ^ 2 := by
    have k : ∀ i, w i * ‖q i - T‖ ^ 2
        = w i * ‖q i‖ ^ 2 - 2 * (w i * inner ℝ (q i) T) + w i * ‖T‖ ^ 2 := by
      intro i; rw [norm_sub_sq_real]; ring
    simp only [k, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hh1 : ∑ i, 2 * (w i * inner ℝ (q i) T) = 2 * ‖T‖ ^ 2 := by
      rw [← Finset.mul_sum, hTT]
    have hh2 : ∑ i, w i * ‖T‖ ^ 2 = ‖T‖ ^ 2 := by rw [← Finset.sum_mul, hw, one_mul]
    rw [hh1, hh2]; ring
  have h3 : ∑ i, w i * (2 * inner ℝ (α i - S) (q i - T))
      = 2 * ∑ i, w i * inner ℝ (α i) (q i) - 2 * inner ℝ S T := by
    have k : ∀ i, w i * (2 * inner ℝ (α i - S) (q i - T))
        = 2 * (w i * inner ℝ (α i) (q i)) - 2 * (w i * inner ℝ (α i) T)
          - 2 * (w i * inner ℝ S (q i)) + 2 * (w i * inner ℝ S T) := by
      intro i; simp only [inner_sub_left, inner_sub_right]; ring
    simp only [k, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have e1 : ∑ i, 2 * (w i * inner ℝ (α i) (q i))
        = 2 * ∑ i, w i * inner ℝ (α i) (q i) := by rw [← Finset.mul_sum]
    have e2 : ∑ i, 2 * (w i * inner ℝ (α i) T) = 2 * inner ℝ S T := by
      rw [← Finset.mul_sum, hST]
    have e3 : ∑ i, 2 * (w i * inner ℝ S (q i)) = 2 * inner ℝ S T := by
      rw [← Finset.mul_sum, hST2]
    have e4 : ∑ i, 2 * (w i * inner ℝ S T) = 2 * inner ℝ S T := by
      have : ∑ i, 2 * (w i * inner ℝ S T) = ∑ i, (2 * inner ℝ S T) * w i := by
        apply Finset.sum_congr rfl; intro i _; ring
      rw [this, ← Finset.mul_sum, hw, mul_one]
    rw [e1, e2, e3, e4]; ring
  have expand : ∑ i, w i * ‖(α i - S) + (q i - T)‖ ^ 2
      = ∑ i, w i * ‖α i - S‖ ^ 2 + ∑ i, w i * ‖q i - T‖ ^ 2
        + ∑ i, w i * (2 * inner ℝ (α i - S) (q i - T)) := by
    have k : ∀ i, w i * ‖(α i - S) + (q i - T)‖ ^ 2
        = w i * ‖α i - S‖ ^ 2 + w i * ‖q i - T‖ ^ 2
          + w i * (2 * inner ℝ (α i - S) (q i - T)) := by
      intro i; rw [norm_add_sq_real]; ring
    rw [show (∑ i, w i * ‖(α i - S) + (q i - T)‖ ^ 2)
          = ∑ i, (w i * ‖α i - S‖ ^ 2 + w i * ‖q i - T‖ ^ 2
            + w i * (2 * inner ℝ (α i - S) (q i - T))) from
        Finset.sum_congr rfl (fun i _ => k i)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hE : ‖S - T‖ ^ 2 + ∑ i, w i * ‖(α i - S) + (q i - T)‖ ^ 2
      = ∑ i, w i * ‖α i‖ ^ 2 + ∑ i, w i * ‖q i‖ ^ 2
        + 2 * ∑ i, w i * inner ℝ (α i) (q i) - 4 * inner ℝ S T := by
    rw [expand, h1, h2, h3, norm_sub_sq_real]; ring
  have hnn : (0:ℝ) ≤ ∑ i, w i * ‖(α i - S) + (q i - T)‖ ^ 2 := by
    apply Finset.sum_nonneg; intro i _
    exact mul_nonneg (hw_nn i) (by positivity)
  have hp : (0:ℝ) ≤ ‖S - T‖ ^ 2 + ∑ i, w i * ‖(α i - S) + (q i - T)‖ ^ 2 := by
    exact add_nonneg (by positivity) hnn
  rw [hE] at hp
  have hA' : ∑ i, ∑ j, w i * w j * ‖α i - q j‖ ^ 2
      = ∑ i, w i * ‖α i‖ ^ 2 + ∑ j, w j * ‖q j‖ ^ 2 - 2 * inner ℝ S T := by
    have hinner : inner ℝ S T = ∑ i, ∑ j, w i * w j * inner ℝ (α i) (q j) := by
      rw [hS, sum_inner]
      apply Finset.sum_congr rfl; intro i _
      rw [real_inner_smul_left, hT, inner_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [real_inner_smul_right]; ring
    have key : ∀ i j, w i * w j * ‖α i - q j‖ ^ 2
        = (w i * w j * ‖α i‖ ^ 2) - 2 * (w i * w j * inner ℝ (α i) (q j))
          + (w j * w i * ‖q j‖ ^ 2) := by
      intro i j; rw [norm_sub_sq_real]; ring
    simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have g1 : ∑ i, ∑ j, w i * w j * ‖α i‖ ^ 2 = ∑ i, w i * ‖α i‖ ^ 2 := by
      apply Finset.sum_congr rfl; intro i _
      rw [show (∑ j, w i * w j * ‖α i‖ ^ 2) = (w i * ‖α i‖ ^ 2) * (∑ j, w j) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring, hw, mul_one]
    have g2 : ∑ i, ∑ j, w j * w i * ‖q j‖ ^ 2 = ∑ j, w j * ‖q j‖ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [show (∑ i, w j * w i * ‖q j‖ ^ 2) = (w j * ‖q j‖ ^ 2) * (∑ i, w i) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring, hw, mul_one]
    have g3 : ∑ x, ∑ x_1, 2 * (w x * w x_1 * inner ℝ (α x) (q x_1))
        = 2 * ∑ x, ∑ x_1, w x * w x_1 * inner ℝ (α x) (q x_1) := by
      simp only [Finset.mul_sum]
    rw [g1, g2, g3, hinner]; ring
  have hB' : ∑ i, w i * ‖α i - q i‖ ^ 2
      = ∑ i, w i * ‖α i‖ ^ 2 + ∑ i, w i * ‖q i‖ ^ 2
        - 2 * ∑ i, w i * inner ℝ (α i) (q i) := by
    have key : ∀ i, w i * ‖α i - q i‖ ^ 2
        = (w i * ‖α i‖ ^ 2) - 2 * (w i * inner ℝ (α i) (q i)) + (w i * ‖q i‖ ^ 2) := by
      intro i; rw [norm_sub_sq_real]; ring
    simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have g3 : ∑ x, 2 * (w x * inner ℝ (α x) (q x))
        = 2 * ∑ x, w x * inner ℝ (α x) (q x) := by simp only [Finset.mul_sum]
    rw [g3]; ring
  rw [hB', hA']
  linarith [hp]

/-- Factor-2 upper bound on the graph edit distance integrality gap under a convex decomposition into permutation matrices. -/
theorem graph_edit_cost_permutation_decomposition_le_two_mul
    {n : ℕ} {ι : Type*} [Fintype ι]
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ_ds : is_doubly_stochastic Q)
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (π : ι → Equiv.Perm (Fin n))
    (hQ : ∑ i, w i • (π i).permMatrix ℝ = Q)
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hB : ∀ i j, B i j = 0 ∨ B i j = 1) :
    ∑ i, w i * perm_edit_cost A B (π i) ≤ 2 * graph_edit_cost A B Q := by
  classical
  have hkey := ged_abstract_ineq (ι := ι) w hw_sum hw_nonneg
    (fun i => gedToE n (fun p : Fin n × Fin n => A ((π i).symm p.1) p.2))
    (fun j => gedToE n (fun p : Fin n × Fin n => B p.1 ((π j) p.2)))
  have hQe : ∀ v ww, Q v ww = ∑ i, w i * (if (π i) v = ww then (1:ℝ) else 0) :=
    ged_Q_entry Q w π hQ
  have hgraph : graph_edit_cost A B Q
      = ∑ i, ∑ j, w i * w j * ‖gedToE n (fun p : Fin n × Fin n => A ((π i).symm p.1) p.2)
          - gedToE n (fun p : Fin n × Fin n => B p.1 ((π j) p.2))‖^2 := by
    rw [ged_graph_eq_sq A B hA hB Q]
    have step : ∀ v v', (∑ ww, ∑ ww', (A v v' - B ww ww') ^ 2 * Q v ww * Q v' ww')
        = ∑ i, ∑ j, w i * w j * (A v v' - B ((π i) v) ((π j) v')) ^ 2 := by
      intro v v'
      rw [← ged_block (fun a b => (A v v' - B a b) ^ 2) w (fun i => (π i) v) (fun j => (π j) v')]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      rw [hQe v x, hQe v' y]
    simp only [step]
    rw [ged_sw4 (fun a b i j => w i * w j * (A a b - B ((π i) a) ((π j) b)) ^ 2)]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [ged_norm_pair A B (π i) (π j)]
    simp only [Finset.mul_sum]
  have hleft : ∑ i, w i * perm_edit_cost A B (π i)
      = ∑ i, w i * ‖gedToE n (fun p : Fin n × Fin n => A ((π i).symm p.1) p.2)
          - gedToE n (fun p : Fin n × Fin n => B p.1 ((π i) p.2))‖^2 := by
    apply Finset.sum_congr rfl; intro i _
    rw [ged_perm_cost_eq A B hA hB (π i), ← ged_norm_pair A B (π i) (π i)]
  rw [hleft, hgraph]
  exact hkey
