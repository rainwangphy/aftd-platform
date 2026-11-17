import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op869_integer_fold_stage_budget

Topic: online_algorithms   Node: 99fafcd7ef16

Provenance: helper lemma. An integer schedule for the fold simulation of arXiv:2610.41516, Section 2.3, toward OP-869.

For an integer m-level fold schedule, each simulation stage fits in the next square-exponent vertex budget and the next power post-degree budget.
-/

lemma op869_ceiling_tmp (m t : ℕ) (ht : 0 < t) :
    (t*m+t-1)/t ≤ m+1 := by
  apply Nat.div_le_of_le_mul
  calc
    t*m+t-1 ≤ t*m+t := Nat.sub_le _ _
    _ = t*(m+1) := by ring

lemma op869_square_budget_tmp (F j : ℕ) (hF : 1 ≤ F) :
    F * F^(j^2) * F^j ≤ F^((j+1)^2) := by
  have he : j^2+j+1 ≤ (j+1)^2 := by nlinarith
  calc
    F * F^(j^2) * F^j = F^(j^2+j+1) := by
      rw [pow_add, pow_succ]
      ring
    _ ≤ F^((j+1)^2) := pow_le_pow_right' hF he

theorem op869_integer_fold_stage_budget (C m j : ℕ) (hC : 1 ≤ C) (hm : 2 ≤ m) (hj : j < m) : let K := m^m; let F := C*K^3*2^(C*(m+1)); let t := m^(m-(j+1)); let q := m^(m-j); C*K^2*q*F^(j^2)*F^j*2^(C*((q+t-1)/t)) ≤ F^((j+1)^2) ∧ C*K^2*q*F^j*2^(C*((q+t-1)/t)) ≤ F^(j+1) := by
  let K := m^m
  let F := C*K^3*2^(C*(m+1))
  let t := m^(m-(j+1))
  let q := m^(m-j)
  change C*K^2*q*F^(j^2)*F^j*2^(C*((q+t-1)/t)) ≤ F^((j+1)^2) ∧
      C*K^2*q*F^j*2^(C*((q+t-1)/t)) ≤ F^(j+1)
  have hm0 : 0 < m := by omega
  have ht : 0 < t := by dsimp [t]; positivity
  have hqt : q = t*m := by
    dsimp [q,t]
    have he : m-j = m-(j+1)+1 := by omega
    rw [he, pow_succ]
  have hqK : q ≤ K := by
    dsimp [q,K]
    exact pow_le_pow_right' (by omega : 1 ≤ m) (by omega)
  have hceil : (q+t-1)/t ≤ m+1 := by rw [hqt]; exact op869_ceiling_tmp m t ht
  have hexp : 2^(C*((q+t-1)/t)) ≤ 2^(C*(m+1)) :=
    pow_le_pow_right' (by norm_num : 1 ≤ 2) (Nat.mul_le_mul_left C hceil)
  have hfac : C*K^2*q*2^(C*((q+t-1)/t)) ≤ F := by
    dsimp [F]
    calc
      C*K^2*q*2^(C*((q+t-1)/t)) ≤ C*K^2*K*2^(C*(m+1)) := by gcongr
      _ = C*K^3*2^(C*(m+1)) := by ring
  have hC0 : 0 < C := by omega
  have hF0 : 0 < F := by dsimp [F,K]; positivity
  have hF : 1 ≤ F := hF0
  constructor
  · calc
      C*K^2*q*F^(j^2)*F^j*2^(C*((q+t-1)/t)) =
          (C*K^2*q*2^(C*((q+t-1)/t))) * F^(j^2)*F^j := by ring
      _ ≤ F * F^(j^2)*F^j := by gcongr
      _ ≤ F^((j+1)^2) := op869_square_budget_tmp F j hF
  · calc
      C*K^2*q*F^j*2^(C*((q+t-1)/t)) =
          (C*K^2*q*2^(C*((q+t-1)/t))) * F^j := by ring
      _ ≤ F * F^j := by gcongr
      _ = F^(j+1) := by rw [pow_succ]; ring
