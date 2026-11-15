import AFTD.Prelude

/-!
# ose_block_metric_quadratic_certificate

Topic: algorithms   Node: 7ba7a8a0228e

Provenance: helper lemma. arXiv:2611.08546, Section 1.1; rational-block negative-direction candidate

For every natural number m, the displayed rational metric on four points per block exists; the signed block vectors have zero total and their squared-distance quadratic form equals 14 times the sum of squared coefficients.
-/

private abbrev oseBlockPoints (m : ℕ) := Bool × (Fin m × Bool)

private noncomputable def oseBlockDist {m : ℕ} (x y : oseBlockPoints m) : ℝ :=
  if x=y then 0 else if x.1 ≠ y.1 ∧ x.2.1 = y.2.1 then 5/2 else 4

private lemma oseBlockDist_lower {m : ℕ} (x y : oseBlockPoints m) (h : x ≠ y) :
    (5 : ℝ)/2 ≤ oseBlockDist x y := by
  unfold oseBlockDist
  simp only [h, if_false]
  split_ifs <;> norm_num

private lemma oseBlockDist_upper {m : ℕ} (x y : oseBlockPoints m) : oseBlockDist x y ≤ 4 := by
  unfold oseBlockDist
  split_ifs <;> norm_num

private noncomputable def oseBlockMetric (m : ℕ) : MetricSpace (oseBlockPoints m) where
  dist := oseBlockDist
  dist_self := by intro x; simp [oseBlockDist]
  dist_comm := by
    intro x y
    by_cases h : x=y
    · subst y; simp [oseBlockDist]
    · have hr : y ≠ x := Ne.symm h
      have hc : (x.1 ≠ y.1 ∧ x.2.1 = y.2.1) ↔ (y.1 ≠ x.1 ∧ y.2.1 = x.2.1) := by
        simp [ne_comm, eq_comm]
      simp only [oseBlockDist,h,hr,if_false,hc]
  dist_triangle := by
    intro x y z
    by_cases hxy : x=y
    · subst y; simp [oseBlockDist]
    by_cases hyz : y=z
    · subst z; simp [oseBlockDist]
    have h1 := oseBlockDist_lower x y hxy
    have h2 := oseBlockDist_lower y z hyz
    have h3 := oseBlockDist_upper x z
    linarith
  eq_of_dist_eq_zero := by
    intro x y h
    by_contra hne
    have hl := oseBlockDist_lower x y hne
    linarith

open scoped BigOperators

private def oseBlockWeight {m : ℕ} (c : Fin m → ℝ) (x : oseBlockPoints m) : ℝ :=
  if x.1 then -c x.2.1 else c x.2.1

private lemma oseBlockLocalSum {m : ℕ} (c : Fin m → ℝ) (i j : Fin m) :
    (∑ a : Bool, ∑ b : Bool, ∑ a' : Bool, ∑ b' : Bool,
      oseBlockWeight c (a,(i,b)) * oseBlockWeight c (a',(j,b')) *
        oseBlockDist (a,(i,b)) (a',(j,b')) ^ 2) =
      if i=j then 14*(c i)^2 else 0 := by
  classical
  by_cases h : i=j
  · subst j
    simp [oseBlockWeight,oseBlockDist,Fintype.sum_bool]
    ring
  · simp [oseBlockWeight,oseBlockDist,Fintype.sum_bool,h,Ne.symm h]

set_option maxHeartbeats 800000 in
private lemma oseBlockDoubleSum {m : ℕ} (g : oseBlockPoints m → oseBlockPoints m → ℝ) :
    (∑ x : oseBlockPoints m, ∑ y : oseBlockPoints m, g x y) =
      ∑ i : Fin m, ∑ j : Fin m, ∑ a : Bool, ∑ b : Bool, ∑ a' : Bool, ∑ b' : Bool,
        g (a,(i,b)) (a',(j,b')) := by
  classical
  let e : ((Fin m × Fin m) × (Bool × Bool × Bool × Bool)) ≃
      (oseBlockPoints m × oseBlockPoints m) := {
    toFun := fun p => ((p.2.1,(p.1.1,p.2.2.1)),(p.2.2.2.1,(p.1.2,p.2.2.2.2)))
    invFun := fun p => ((p.1.2.1,p.2.2.1),(p.1.1,p.1.2.2,p.2.1,p.2.2.2))
    left_inv := by rintro ⟨⟨i,j⟩,a,b,c,d⟩; rfl
    right_inv := by rintro ⟨⟨a,i,b⟩,c,j,d⟩; rfl
  }
  calc
    (∑ x : oseBlockPoints m, ∑ y : oseBlockPoints m, g x y) =
        ∑ p : oseBlockPoints m × oseBlockPoints m, g p.1 p.2 := (Fintype.sum_prod_type (fun p : oseBlockPoints m × oseBlockPoints m => g p.1 p.2)).symm
    _ = ∑ z : ((Fin m × Fin m) × (Bool × Bool × Bool × Bool)), g (e z).1 (e z).2 :=
      (e.sum_comp _).symm
    _ = _ := by simp only [Fintype.sum_prod_type]; rfl

private lemma oseBlockGlobalSum {m : ℕ} (c : Fin m → ℝ) :
    (∑ x : oseBlockPoints m, ∑ y : oseBlockPoints m,
      oseBlockWeight c x * oseBlockWeight c y * oseBlockDist x y ^ 2) =
      14 * ∑ i : Fin m, (c i)^2 := by
  classical
  rw [oseBlockDoubleSum]
  simp only [oseBlockLocalSum]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mul_sum]

private noncomputable def oseBlockWitness {m : ℕ} (i : Fin m) (x : oseBlockPoints m) : ℝ :=
  if x.2.1 = i then (if x.1 then -1 else 1) else 0

private lemma oseBlockWitness_sum {m : ℕ} (i : Fin m) :
    (∑ x : oseBlockPoints m, oseBlockWitness i x) = 0 := by
  classical
  simp [oseBlockWitness,Fintype.sum_prod_type,Fintype.sum_bool,Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.sum_ite_eq']

private lemma oseBlockWitness_combo {m : ℕ} (c : Fin m → ℝ) (x : oseBlockPoints m) :
    (∑ i : Fin m, c i * oseBlockWitness i x) = oseBlockWeight c x := by
  classical
  rcases x with ⟨a,j,b⟩
  cases a <;> simp [oseBlockWitness,oseBlockWeight,mul_ite,Finset.sum_ite_eq,Finset.sum_ite_eq',eq_comm]

private lemma oseBlockQuadraticIdentity {m : ℕ} (c : Fin m → ℝ) :
    (∑ x : oseBlockPoints m, ∑ y : oseBlockPoints m,
      (∑ i : Fin m, c i * oseBlockWitness i x) *
      (∑ i : Fin m, c i * oseBlockWitness i y) * oseBlockDist x y ^ 2) =
      14 * ∑ i : Fin m, (c i)^2 := by
  simp only [oseBlockWitness_combo]
  exact oseBlockGlobalSum c

theorem ose_block_metric_quadratic_certificate (m : ℕ) :
    let X := Bool × (Fin m × Bool)
    let w : Fin m → X → ℝ := fun i x => if x.2.1 = i then (if x.1 then -1 else 1) else 0
    ∃ M : MetricSpace X, letI := M
      (∀ x y : X, dist x y = if x = y then 0 else if x.1 ≠ y.1 ∧ x.2.1 = y.2.1 then (5 : ℝ)/2 else 4) ∧
      (∀ i : Fin m, ∑ x : X, w i x = 0) ∧
      ∀ c : Fin m → ℝ, (∑ x : X, ∑ y : X,
        (∑ i : Fin m, c i * w i x) * (∑ i : Fin m, c i * w i y) * dist x y ^ 2) =
          14 * ∑ i : Fin m, (c i)^2 := by
  dsimp only
  refine ⟨oseBlockMetric m, ?_, ?_, ?_⟩
  · intro x y; rfl
  · intro i
    exact oseBlockWitness_sum i
  · intro c
    exact oseBlockQuadraticIdentity c
