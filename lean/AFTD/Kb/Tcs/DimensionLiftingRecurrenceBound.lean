import AFTD.Prelude

/-!
# dimension_lifting_recurrence_bound

Topic: combinatorics   Node: e8542ffdbbc5

Provenance: formalization of a published result. Source: arXiv:2610.16703 (Piercing boxes and products of trees), Lemma 2.3.

Let f(p, d) ≥ 0 and g(p) ≥ 0 with g nondecreasing, f(p, k) ≤ p·g(p) for p ≥ 1, and for every p ≥ 1, d > k there are positive integers p_i ≤ p/2 with Σ p_i ≤ p and f(p, d) ≤ f(p, d−1) + Σ f(p_i, d). Then f(p, d) ≤ p·g(p)·C(⌊log₂ p⌋ + d − k, d − k) for all p ≥ 1, d ≥ k.
-/

lemma dimension_lifting_recurrence_bound_choose_pascal_step (L m : ℕ) (hL : 1 ≤ L) :
    (L + m).choose m + (L - 1 + (m + 1)).choose (m + 1) = (L + (m + 1)).choose (m + 1) := by
  have heq : L - 1 + (m + 1) = L + m := by lia
  rw [heq]
  have h_id := (Nat.choose_succ_succ (L + m) m).symm
  have heq2 : (L + m).succ = L + (m + 1) := by lia
  rw [heq2] at h_id
  exact h_id

lemma dimension_lifting_recurrence_bound_list_sum_bound (ps : List ℕ) (f : ℕ → ℝ) (C : ℝ)
    (h : ∀ x ∈ ps, f x ≤ (x : ℝ) * C) :
    (ps.map f).sum ≤ (ps.sum : ℝ) * C := by
  induction ps with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    have hx : f x ≤ (x : ℝ) * C := h x (List.mem_cons_self ..)
    have hxs : (xs.map f).sum ≤ (xs.sum : ℝ) * C :=
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    linarith

theorem dimension_lifting_recurrence_bound (k : ℕ) (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hf : ∀ p d, 0 ≤ f p d) (hg : ∀ p, 0 ≤ g p) (hmono : Monotone g)
    (hbase : ∀ p, 1 ≤ p → f p k ≤ p * g p)
    (hrec : ∀ p, 1 ≤ p → ∀ d, k < d → ∃ ps : List ℕ, (∀ x ∈ ps, 1 ≤ x ∧ 2 * x ≤ p) ∧
      ps.sum ≤ p ∧ f p d ≤ f p (d - 1) + (ps.map (fun x => f x d)).sum) :
    ∀ p, 1 ≤ p → ∀ d, k ≤ d → f p d ≤ p * g p * ((Nat.log 2 p + (d - k)).choose (d - k)) := by
  have H : ∀ m : ℕ, ∀ p, 1 ≤ p → f p (k + m) ≤ p * g p * ((Nat.log 2 p + m).choose m) := by
    intro m
    induction m with
    | zero =>
      intro p hp
      simp only [add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
      exact hbase p hp
    | succ m ih =>
      intro p
      induction p using Nat.strong_induction_on with
      | h p ih_p =>
        intro hp
        rcases (Nat.lt_or_ge 1 p) with hp_gt | hp_le
        · -- p ≥ 2
          have hp2 : 2 ≤ p := hp_gt
          obtain ⟨ps, hps_prop, hps_sum, hrec_le⟩ := hrec p hp (k + (m + 1)) (by lia)
          have h_pred : k + (m + 1) - 1 = k + m := by lia
          rw [h_pred] at hrec_le
          have h_ih_p : f p (k + m) ≤ p * g p * ((Nat.log 2 p + m).choose m) := ih p hp
          let C : ℝ := g p * ((Nat.log 2 p - 1 + (m + 1)).choose (m + 1) : ℝ)
          have h_elem : ∀ x ∈ ps, f x (k + (m + 1)) ≤ (x : ℝ) * C := by
            intro x hx
            have hx_prop := hps_prop x hx
            have hx1 : 1 ≤ x := hx_prop.1
            have hxp : 2 * x ≤ p := hx_prop.2
            have hx_lt_p : x < p := by lia
            have hx_ih := ih_p x hx_lt_p hx1
            have hx_le_p : x ≤ p := by lia
            have hg_le : g x ≤ g p := hmono hx_le_p
            have hlog_le : Nat.log 2 x + 1 ≤ Nat.log 2 p := by
              have h1 : Nat.log 2 (x * 2) ≤ Nat.log 2 p := by
                rw [Nat.mul_comm]
                exact Nat.log_mono_right hxp
              have h2 : Nat.log 2 (x * 2) = Nat.log 2 x + 1 :=
                Nat.log_mul_base (by decide) (by lia)
              rwa [h2] at h1
            have hchoose_le : (Nat.log 2 x + (m + 1)).choose (m + 1) ≤
                (Nat.log 2 p - 1 + (m + 1)).choose (m + 1) :=
              Nat.choose_le_choose (m + 1) (by lia)
            refine hx_ih.trans ?_
            have h1 : (x : ℝ) * g x ≤ (x : ℝ) * g p :=
              mul_le_mul_of_nonneg_left hg_le (Nat.cast_nonneg x)
            have hstep1 : (x : ℝ) * g x * ((Nat.log 2 x + (m + 1)).choose (m + 1) : ℝ) ≤
                (x : ℝ) * g p * ((Nat.log 2 x + (m + 1)).choose (m + 1) : ℝ) :=
              mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
            have hchoose_cast : ((Nat.log 2 x + (m + 1)).choose (m + 1) : ℝ) ≤
                ((Nat.log 2 p - 1 + (m + 1)).choose (m + 1) : ℝ) := by
              exact_mod_cast hchoose_le
            have hstep2 : (x : ℝ) * g p * ((Nat.log 2 x + (m + 1)).choose (m + 1) : ℝ) ≤
                (x : ℝ) * g p * ((Nat.log 2 p - 1 + (m + 1)).choose (m + 1) : ℝ) :=
              mul_le_mul_of_nonneg_left hchoose_cast (mul_nonneg (Nat.cast_nonneg x) (hg p))
            have hstep_comb : (x : ℝ) * g x * ((Nat.log 2 x + (m + 1)).choose (m + 1) : ℝ) ≤
                (x : ℝ) * g p * ((Nat.log 2 p - 1 + (m + 1)).choose (m + 1) : ℝ) :=
              hstep1.trans hstep2
            have heq_C : (x : ℝ) * g p * ((Nat.log 2 p - 1 + (m + 1)).choose (m + 1) : ℝ) =
                (x : ℝ) * C := by
              dsimp [C]
              ring
            rw [heq_C] at hstep_comb
            exact hstep_comb
          have h_sum_le := dimension_lifting_recurrence_bound_list_sum_bound ps (fun x => f x (k + (m + 1))) C h_elem
          have hC_nonneg : 0 ≤ C := mul_nonneg (hg p) (Nat.cast_nonneg _)
          have h_sum_le_p : (ps.sum : ℝ) * C ≤ (p : ℝ) * C := by
            have : (ps.sum : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hps_sum
            nlinarith
          have h_sum_final : (ps.map (fun x => f x (k + (m + 1)))).sum ≤ (p : ℝ) * C :=
            h_sum_le.trans h_sum_le_p
          have hL_pos : 1 ≤ Nat.log 2 p := Nat.log_pos (by decide) hp2
          have h_pascal := dimension_lifting_recurrence_bound_choose_pascal_step (Nat.log 2 p) m hL_pos
          have h_pascal_R : ((Nat.log 2 p + m).choose m : ℝ) +
              ((Nat.log 2 p - 1 + (m + 1)).choose (m + 1) : ℝ) =
              ((Nat.log 2 p + (m + 1)).choose (m + 1) : ℝ) := by
            exact_mod_cast h_pascal
          have h_sum_bound : (p : ℝ) * C =
              (p : ℝ) * g p * ((Nat.log 2 p - 1 + (m + 1)).choose (m + 1) : ℝ) := by
            dsimp [C]
            ring
          rw [h_sum_bound] at h_sum_final
          refine hrec_le.trans ?_
          calc f p (k + m) + (ps.map (fun x => f x (k + (m + 1)))).sum
            ≤ (p : ℝ) * g p * ((Nat.log 2 p + m).choose m : ℝ) +
              (p : ℝ) * g p * ((Nat.log 2 p - 1 + (m + 1)).choose (m + 1) : ℝ) :=
              add_le_add h_ih_p h_sum_final
            _ = (p : ℝ) * g p * (((Nat.log 2 p + m).choose m : ℝ) +
              ((Nat.log 2 p - 1 + (m + 1)).choose (m + 1) : ℝ)) := by ring
            _ = (p : ℝ) * g p * ((Nat.log 2 p + (m + 1)).choose (m + 1) : ℝ) := by rw [h_pascal_R]
        · -- p = 1
          have hp1 : p = 1 := by lia
          subst hp1
          obtain ⟨ps, hps_prop, _, hrec_le⟩ := hrec 1 (by lia) (k + (m + 1)) (by lia)
          have hps_nil : ps = [] := by
            cases ps with
            | nil => rfl
            | cons x xs =>
              have := (hps_prop x (List.mem_cons_self ..)).2
              have := (hps_prop x (List.mem_cons_self ..)).1
              lia
          rw [hps_nil] at hrec_le
          simp only [List.map_nil, List.sum_nil, add_zero] at hrec_le
          have h_pred : k + (m + 1) - 1 = k + m := by lia
          rw [h_pred] at hrec_le
          have h_ih := ih 1 (by lia)
          have h_log : Nat.log 2 1 = 0 := Nat.log_one_right 2
          rw [h_log] at h_ih ⊢
          simp only [zero_add, Nat.choose_self, Nat.cast_one, mul_one] at h_ih ⊢
          exact hrec_le.trans h_ih
  intro p hp d hd
  have h := H (d - k) p hp
  rwa [Nat.add_sub_of_le hd] at h
