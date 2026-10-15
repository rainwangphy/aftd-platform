import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianPellSide

/-!
# mondrian_pell_side_eq

Topic: combinatorics   Node: 550ac10a565e

Provenance: helper lemma. arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), proof of Theorem 1.1 (the norm −2 Pell family); serves mondrian_pell_family_defect_280.

Each n_j equals 105 q_j for odd p_j, q_j with q_j < p_j < 7q_j and p_j² − 19 q_j² = −2, where (p₀, q₀) = (13, 3) and (p_{j+1}, q_{j+1}) = (170p_j + 741q_j, 39p_j + 170q_j).
-/

def mondrian_pell_side_eq_pair : ℕ → ℕ × ℕ
  | 0 => (13, 3)
  | j + 1 =>
    let pq := mondrian_pell_side_eq_pair j
    (170 * pq.1 + 741 * pq.2, 39 * pq.1 + 170 * pq.2)

def mondrian_pell_side_eq_p (j : ℕ) : ℕ := (mondrian_pell_side_eq_pair j).1
def mondrian_pell_side_eq_q (j : ℕ) : ℕ := (mondrian_pell_side_eq_pair j).2

lemma mondrian_pell_side_eq_pell (j : ℕ) :
    (mondrian_pell_side_eq_p j : ℤ) ^ 2 - 19 * (mondrian_pell_side_eq_q j : ℤ) ^ 2 = -2 := by
  induction j with
  | zero => decide
  | succ n ih =>
    have hP : (mondrian_pell_side_eq_p (n + 1) : ℤ) =
        170 * (mondrian_pell_side_eq_p n : ℤ) + 741 * (mondrian_pell_side_eq_q n : ℤ) := by
      push_cast [mondrian_pell_side_eq_p]; rfl
    have hQ : (mondrian_pell_side_eq_q (n + 1) : ℤ) =
        39 * (mondrian_pell_side_eq_p n : ℤ) + 170 * (mondrian_pell_side_eq_q n : ℤ) := by
      push_cast [mondrian_pell_side_eq_q]; rfl
    have id : ∀ p q : ℤ, (170 * p + 741 * q) ^ 2 - 19 * (39 * p + 170 * q) ^ 2 = p ^ 2 - 19 * q ^ 2 := by
      intro p q; ring
    rw [hP, hQ, id, ih]

lemma mondrian_pell_side_eq_bounds (j : ℕ) :
    mondrian_pell_side_eq_p j % 2 = 1 ∧
    mondrian_pell_side_eq_q j % 2 = 1 ∧
    mondrian_pell_side_eq_q j < mondrian_pell_side_eq_p j ∧
    mondrian_pell_side_eq_p j < 7 * mondrian_pell_side_eq_q j := by
  induction j with
  | zero => decide
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have hP : mondrian_pell_side_eq_p (n + 1) = 170 * mondrian_pell_side_eq_p n + 741 * mondrian_pell_side_eq_q n := rfl
    have hQ : mondrian_pell_side_eq_q (n + 1) = 39 * mondrian_pell_side_eq_p n + 170 * mondrian_pell_side_eq_q n := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hP]; omega
    · rw [hQ]; omega
    · rw [hP, hQ]; omega
    · rw [hP, hQ]; omega

lemma mondrian_pell_side_eq_q_step (j : ℕ) :
    mondrian_pell_side_eq_q (j + 2) + mondrian_pell_side_eq_q j = 340 * mondrian_pell_side_eq_q (j + 1) := by
  have h1 : mondrian_pell_side_eq_q (j + 2) =
      39 * mondrian_pell_side_eq_p (j + 1) + 170 * mondrian_pell_side_eq_q (j + 1) := rfl
  have h2 : mondrian_pell_side_eq_p (j + 1) =
      170 * mondrian_pell_side_eq_p j + 741 * mondrian_pell_side_eq_q j := rfl
  have h3 : mondrian_pell_side_eq_q (j + 1) =
      39 * mondrian_pell_side_eq_p j + 170 * mondrian_pell_side_eq_q j := rfl
  rw [h1, h2, h3]
  omega

lemma mondrian_pell_side_eq_side (j : ℕ) :
    mondrian_pell_side j = 105 * mondrian_pell_side_eq_q j := by
  have key : ∀ k, mondrian_pell_side k = 105 * mondrian_pell_side_eq_q k ∧
      mondrian_pell_side (k + 1) = 105 * mondrian_pell_side_eq_q (k + 1) := by
    intro k
    induction k with
    | zero =>
      decide
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨h2, ?_⟩
      have e : mondrian_pell_side (n + 2) = 340 * mondrian_pell_side (n + 1) - mondrian_pell_side n := rfl
      have hstep := mondrian_pell_side_eq_q_step n
      change mondrian_pell_side (n + 2) = 105 * mondrian_pell_side_eq_q (n + 2)
      rw [e, h1, h2]
      omega
  exact (key j).1

theorem mondrian_pell_side_eq (j : ℕ) :
    ∃ p q : ℕ, p % 2 = 1 ∧ q % 2 = 1 ∧ q < p ∧ p < 7 * q ∧
      (p : ℤ) ^ 2 - 19 * (q : ℤ) ^ 2 = -2 ∧ mondrian_pell_side j = 105 * q := by
  use mondrian_pell_side_eq_p j, mondrian_pell_side_eq_q j
  obtain ⟨h1, h2, h3, h4⟩ := mondrian_pell_side_eq_bounds j
  exact ⟨h1, h2, h3, h4, mondrian_pell_side_eq_pell j, mondrian_pell_side_eq_side j⟩
