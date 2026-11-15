import AFTD.Prelude
import AFTD.Kb.Tcs.OseQuadInequality

/-!
# ose_cube_hilbert_antipodal_inequality

Topic: algorithms   Node: 7fc543bcad8b

Provenance: helper lemma. arXiv:2611.08546, Section 6, and the Hilbert-space antipodal inequality on the Boolean cube

For any map from the Boolean n-cube into a real inner-product space, the sum of squared antipodal distances is at most the sum over all cube edges, counted at each endpoint, of squared image distances.
-/

open scoped BigOperators

private def ose_cube_anti {n : ℕ} (x : Fin n → Bool) : Fin n → Bool := fun i => !(x i)
private def ose_cube_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!(x i))

private lemma ose_cube_anti_involutive {n : ℕ} : Function.Involutive (@ose_cube_anti n) := by
  intro x
  funext i
  simp [ose_cube_anti]

private def ose_cube_anti_equiv (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := ose_cube_anti
  invFun := ose_cube_anti
  left_inv := ose_cube_anti_involutive
  right_inv := ose_cube_anti_involutive

private lemma ose_cube_anti_cons {n : ℕ} (b : Bool) (x : Fin n → Bool) :
    ose_cube_anti (Fin.cons b x) = Fin.cons (!b) (ose_cube_anti x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [ose_cube_anti]

private lemma ose_cube_flip_cons_zero {n : ℕ} (b : Bool) (x : Fin n → Bool) :
    ose_cube_flip (Fin.cons b x) 0 = Fin.cons (!b) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [ose_cube_flip, Function.update]

private lemma ose_cube_flip_cons_succ {n : ℕ} (b : Bool) (x : Fin n → Bool) (i : Fin n) :
    ose_cube_flip (Fin.cons b x) i.succ = Fin.cons b (ose_cube_flip x i) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · have hz : (0 : Fin (n+1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
    simp [ose_cube_flip, Function.update, hz]
  · by_cases h : k = i
    · subst k; simp [ose_cube_flip, Function.update]
    · simp [ose_cube_flip, Function.update, h]

private lemma ose_cube_sum_cons (n : ℕ) (g : (Fin (n+1) → Bool) → ℝ) :
    (∑ x, g x) = ∑ x : Fin n → Bool, (g (Fin.cons false x) + g (Fin.cons true x)) := by
  calc
    (∑ x, g x) = ∑ p : Bool × (Fin n → Bool), g (Fin.cons p.1 p.2) :=
      ((Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp g).symm
    _ = ∑ b : Bool, ∑ x : Fin n → Bool, g (Fin.cons b x) := Fintype.sum_prod_type _
    _ = ∑ x : Fin n → Bool, (g (Fin.cons false x) + g (Fin.cons true x)) := by
      simp [Fintype.sum_bool, Finset.sum_add_distrib, add_comm]

private theorem ose_antipodal_aux (n : ℕ) : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : (Fin n → Bool) → H),
    (∑ x : Fin n → Bool, dist (f x) (f (ose_cube_anti x)) ^ 2) ≤
      ∑ x : Fin n → Bool, ∑ i : Fin n, dist (f x) (f (ose_cube_flip x i)) ^ 2 := by
  induction n with
  | zero =>
    intro H _ _ f
    have ha (x : Fin 0 → Bool) : ose_cube_anti x = x := by
      funext i
      exact Fin.elim0 i
    simp [ha]
  | succ n ih =>
    intro H _ _ f
    let f0 : (Fin n → Bool) → H := fun x => f (Fin.cons false x)
    let f1 : (Fin n → Bool) → H := fun x => f (Fin.cons true x)
    let J : (Fin n → Bool) → ℝ := fun x => dist (f0 x) (f1 x)^2
    let E : ℝ := ∑ x, J x
    let A0 : ℝ := ∑ x, dist (f0 x) (f0 (ose_cube_anti x))^2
    let A1 : ℝ := ∑ x, dist (f1 x) (f1 (ose_cube_anti x))^2
    let T0 : ℝ := ∑ x, ∑ i : Fin n, dist (f0 x) (f0 (ose_cube_flip x i))^2
    let T1 : ℝ := ∑ x, ∑ i : Fin n, dist (f1 x) (f1 (ose_cube_flip x i))^2
    let L : ℝ := ∑ x, (dist (f0 x) (f1 (ose_cube_anti x))^2 +
      dist (f1 x) (f0 (ose_cube_anti x))^2)
    have hpoint (x : Fin n → Bool) :
        dist (f0 x) (f1 (ose_cube_anti x))^2 + dist (f1 x) (f0 (ose_cube_anti x))^2 ≤
          J x + J (ose_cube_anti x) + dist (f0 x) (f0 (ose_cube_anti x))^2 +
          dist (f1 x) (f1 (ose_cube_anti x))^2 := by
      exact ose_quad_inequality H (f0 x) (f1 x) (f0 (ose_cube_anti x)) (f1 (ose_cube_anti x))
    have hL : L ≤ ∑ x : Fin n → Bool,
        (J x + J (ose_cube_anti x) + dist (f0 x) (f0 (ose_cube_anti x))^2 +
          dist (f1 x) (f1 (ose_cube_anti x))^2) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hpoint x
    have hJ : (∑ x, J (ose_cube_anti x)) = ∑ x, J x :=
      (ose_cube_anti_equiv n).sum_comp J
    have hsum : (∑ x : Fin n → Bool,
        (J x + J (ose_cube_anti x) + dist (f0 x) (f0 (ose_cube_anti x))^2 +
          dist (f1 x) (f1 (ose_cube_anti x))^2)) = E+E+A0+A1 := by
      simp only [Finset.sum_add_distrib]
      rw [hJ]
    rw [hsum] at hL
    have h0 : A0 ≤ T0 := ih H f0
    have h1 : A1 ≤ T1 := ih H f1
    have hleft : (∑ x : Fin (n+1) → Bool, dist (f x) (f (ose_cube_anti x))^2) = L := by
      rw [ose_cube_sum_cons]
      simp [L, f0, f1, ose_cube_anti_cons]
    have hright : (∑ x : Fin (n+1) → Bool, ∑ i : Fin (n+1),
        dist (f x) (f (ose_cube_flip x i))^2) = E+E+T0+T1 := by
      rw [ose_cube_sum_cons]
      simp only [Fin.sum_univ_succ, ose_cube_flip_cons_zero, ose_cube_flip_cons_succ]
      simp only [Finset.sum_add_distrib]
      simp only [E,T0,T1,J,f0,f1]
      simp only [Bool.not_false, Bool.not_true, dist_comm, add_comm, add_left_comm, add_assoc]
    rw [hleft,hright]
    linarith

theorem ose_cube_hilbert_antipodal_inequality (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : (Fin n → Bool) → H) : (∑ x : Fin n → Bool, dist (f x) (f (fun i => !(x i))) ^ 2) ≤ ∑ x : Fin n → Bool, ∑ i : Fin n, dist (f x) (f (Function.update x i (!(x i)))) ^ 2 := by
  change (∑ x : Fin n → Bool, dist (f x) (f (ose_cube_anti x)) ^ 2) ≤
    ∑ x : Fin n → Bool, ∑ i : Fin n, dist (f x) (f (ose_cube_flip x i)) ^ 2
  exact ose_antipodal_aux n H f
