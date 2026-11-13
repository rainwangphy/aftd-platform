import AFTD.Prelude

/-!
# single_interval_gap_quarter_chunk_10_20

Topic: combinatorics   Node: 5281a45083b7

Provenance: helper lemma. Finite gap certificate for OP-1482; independently verified by experiment 25549.

On the specified rational interval of t, the nineteen points −t k²−βk have a circular gap of length greater than t for some real β.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 4096

theorem interval_gap_piece_10 (t : ℝ) (hl : ((1 : ℝ) / 14) ≤ t) (hu : t < ((27 : ℝ) / 343)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨((5 : ℝ) / 14) - (20 : ℝ) * t, (99 : ℝ) * t + ((-97 : ℝ) / 14), (51 : ℝ) * t + ((-43 : ℝ) / 14), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_11 (t : ℝ) (hl : ((27 : ℝ) / 343) ≤ t) (hu : t < ((33 : ℝ) / 392)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨((11 : ℝ) / 16) - (16 : ℝ) * t, (63 : ℝ) * t + ((-77 : ℝ) / 16), (15 : ℝ) * t + ((-11 : ℝ) / 16), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(10 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(12 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(14 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(16 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_12 (t : ℝ) (hl : ((33 : ℝ) / 392) ≤ t) (hu : t < ((9 : ℝ) / 100)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨((1 : ℝ) / 2) - (18 : ℝ) * t, (81 : ℝ) * t + ((-13 : ℝ) / 2), (32 : ℝ) * t + (-2 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(10 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_13 (t : ℝ) (hl : ((9 : ℝ) / 100) ≤ t) (hu : t < ((1 : ℝ) / 10)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨((1 : ℝ) / 2) - (18 : ℝ) * t, (56 : ℝ) * t + (-5 : ℝ), (80 : ℝ) * t + (-7 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(10 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_14 (t : ℝ) (hl : ((1 : ℝ) / 10) ≤ t) (hu : t < ((3 : ℝ) / 28)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨((1 : ℝ) / 2) - (18 : ℝ) * t, (77 : ℝ) * t + ((-15 : ℝ) / 2), (56 : ℝ) * t + (-5 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(10 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_15 (t : ℝ) (hl : ((3 : ℝ) / 28) ≤ t) (hu : t < ((1 : ℝ) / 9)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨(0 : ℝ) - (16 : ℝ) * t, (39 : ℝ) * t + (-4 : ℝ), (60 : ℝ) * t + (-6 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_16 (t : ℝ) (hl : ((1 : ℝ) / 9) ≤ t) (hu : t < ((2 : ℝ) / 17)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨(0 : ℝ) - (18 : ℝ) * t, (65 : ℝ) * t + (-7 : ℝ), (32 : ℝ) * t + (-3 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_17 (t : ℝ) (hl : ((2 : ℝ) / 17) ≤ t) (hu : t < ((4 : ℝ) / 33)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨(0 : ℝ) - (16 : ℝ) * t, (60 : ℝ) * t + (-7 : ℝ), (28 : ℝ) * t + (-3 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_18 (t : ℝ) (hl : ((4 : ℝ) / 33) ≤ t) (hu : t < ((1 : ℝ) / 8)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨(0 : ℝ) - (18 : ℝ) * t, (17 : ℝ) * t + (-2 : ℝ), (77 : ℝ) * t + (-9 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_19 (t : ℝ) (hl : ((1 : ℝ) / 8) ≤ t) (hu : t < ((2 : ℝ) / 15)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨(0 : ℝ) - (18 : ℝ) * t, (81 : ℝ) * t + (-10 : ℝ), (45 : ℝ) * t + (-5 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem single_interval_gap_quarter_chunk_10_20 (t : ℝ) (hl : ((1 : ℝ) / 14) ≤ t) (hu : t < ((2 : ℝ) / 15)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  by_cases hcut : t < ((27 : ℝ) / 343)
  · exact interval_gap_piece_10 t hl hcut
  · have hnext : ((27 : ℝ) / 343) ≤ t := le_of_not_gt hcut
    clear hl hcut
    have hl := hnext
    clear hnext
    by_cases hcut : t < ((33 : ℝ) / 392)
    · exact interval_gap_piece_11 t hl hcut
    · have hnext : ((33 : ℝ) / 392) ≤ t := le_of_not_gt hcut
      clear hl hcut
      have hl := hnext
      clear hnext
      by_cases hcut : t < ((9 : ℝ) / 100)
      · exact interval_gap_piece_12 t hl hcut
      · have hnext : ((9 : ℝ) / 100) ≤ t := le_of_not_gt hcut
        clear hl hcut
        have hl := hnext
        clear hnext
        by_cases hcut : t < ((1 : ℝ) / 10)
        · exact interval_gap_piece_13 t hl hcut
        · have hnext : ((1 : ℝ) / 10) ≤ t := le_of_not_gt hcut
          clear hl hcut
          have hl := hnext
          clear hnext
          by_cases hcut : t < ((3 : ℝ) / 28)
          · exact interval_gap_piece_14 t hl hcut
          · have hnext : ((3 : ℝ) / 28) ≤ t := le_of_not_gt hcut
            clear hl hcut
            have hl := hnext
            clear hnext
            by_cases hcut : t < ((1 : ℝ) / 9)
            · exact interval_gap_piece_15 t hl hcut
            · have hnext : ((1 : ℝ) / 9) ≤ t := le_of_not_gt hcut
              clear hl hcut
              have hl := hnext
              clear hnext
              by_cases hcut : t < ((2 : ℝ) / 17)
              · exact interval_gap_piece_16 t hl hcut
              · have hnext : ((2 : ℝ) / 17) ≤ t := le_of_not_gt hcut
                clear hl hcut
                have hl := hnext
                clear hnext
                by_cases hcut : t < ((4 : ℝ) / 33)
                · exact interval_gap_piece_17 t hl hcut
                · have hnext : ((4 : ℝ) / 33) ≤ t := le_of_not_gt hcut
                  clear hl hcut
                  have hl := hnext
                  clear hnext
                  by_cases hcut : t < ((1 : ℝ) / 8)
                  · exact interval_gap_piece_18 t hl hcut
                  · have hnext : ((1 : ℝ) / 8) ≤ t := le_of_not_gt hcut
                    clear hl hcut
                    have hl := hnext
                    clear hnext
                    exact interval_gap_piece_19 t hl hu
