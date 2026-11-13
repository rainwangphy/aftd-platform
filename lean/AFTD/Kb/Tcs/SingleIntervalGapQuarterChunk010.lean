import AFTD.Prelude

/-!
# single_interval_gap_quarter_chunk_0_10

Topic: combinatorics   Node: 54fc5c5ef7ac

Provenance: helper lemma. Finite gap certificate for OP-1482; independently verified by experiment 25549.

On the specified rational interval of t, the nineteen points −t k²−βk have a circular gap of length greater than t for some real β.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 4096

theorem interval_gap_piece_0 (t : ℝ) (hl : (0 : ℝ) ≤ t) (hu : t < ((2 : ℝ) / 153)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨((16 : ℝ) / 17) - (17 : ℝ) * t, (30 : ℝ) * t + ((2 : ℝ) / 17), (42 : ℝ) * t + ((3 : ℝ) / 17), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(10 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(11 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(12 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(13 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(14 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(15 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(16 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(17 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(18 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_1 (t : ℝ) (hl : ((2 : ℝ) / 153) ≤ t) (hu : t < ((1 : ℝ) / 49)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨(0 : ℝ) - (18 : ℝ) * t, (32 : ℝ) * t + (0 : ℝ), (45 : ℝ) * t + (0 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_2 (t : ℝ) (hl : ((1 : ℝ) / 49) ≤ t) (hu : t < ((1 : ℝ) / 37)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨((1 : ℝ) / 2) - (20 : ℝ) * t, (100 : ℝ) * t + (-2 : ℝ), (64 : ℝ) * t + (-1 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_3 (t : ℝ) (hl : ((1 : ℝ) / 37) ≤ t) (hu : t < ((1 : ℝ) / 30)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨((1 : ℝ) / 2) - (16 : ℝ) * t, (48 : ℝ) * t + (-1 : ℝ), (39 : ℝ) * t + ((-1 : ℝ) / 2), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(10 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(11 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_4 (t : ℝ) (hl : ((1 : ℝ) / 30) ≤ t) (hu : t < ((2 : ℝ) / 49)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨(0 : ℝ) - (18 : ℝ) * t, (32 : ℝ) * t + (-1 : ℝ), (65 : ℝ) * t + (-2 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_5 (t : ℝ) (hl : ((2 : ℝ) / 49) ≤ t) (hu : t < ((2 : ℝ) / 45)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨((7 : ℝ) / 15) - (17 : ℝ) * t, (42 : ℝ) * t + ((-7 : ℝ) / 5), (66 : ℝ) * t + ((-32 : ℝ) / 15), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(5 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(6 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(7 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(8 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(9 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(10 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_6 (t : ℝ) (hl : ((2 : ℝ) / 45) ≤ t) (hu : t < ((1 : ℝ) / 20)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨(0 : ℝ) - (18 : ℝ) * t, (45 : ℝ) * t + (-2 : ℝ), (72 : ℝ) * t + (-3 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_7 (t : ℝ) (hl : ((1 : ℝ) / 20) ≤ t) (hu : t < ((1 : ℝ) / 17)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨(0 : ℝ) - (16 : ℝ) * t, (48 : ℝ) * t + (-2 : ℝ), (15 : ℝ) * t + (0 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_8 (t : ℝ) (hl : ((1 : ℝ) / 17) ≤ t) (hu : t < ((2 : ℝ) / 31)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨(0 : ℝ) - (17 : ℝ) * t, (72 : ℝ) * t + (-4 : ℝ), (42 : ℝ) * t + (-2 : ℝ), ?_, ?_⟩
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
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem interval_gap_piece_9 (t : ℝ) (hl : ((2 : ℝ) / 31) ≤ t) (hu : t < ((1 : ℝ) / 14)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  refine ⟨(0 : ℝ) - (18 : ℝ) * t, (81 : ℝ) * t + (-5 : ℝ), (56 : ℝ) * t + (-3 : ℝ), ?_, ?_⟩
  · linarith
  · intro k
    fin_cases k
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-4 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-3 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-2 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(-1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(0 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨(1 : ℤ), ?_, ?_⟩ <;> norm_num <;> linarith

theorem single_interval_gap_quarter_chunk_0_10 (t : ℝ) (hl : (0 : ℝ) ≤ t) (hu : t < ((1 : ℝ) / 14)) :
    ∃ β a b : ℝ, t < b - a ∧
      ∀ k : Fin 19, ∃ z : ℤ,
        b ≤ -(k.val : ℝ)^2 * t - β * k.val + z ∧
        -(k.val : ℝ)^2 * t - β * k.val + z ≤ a + 1 := by
  by_cases hcut : t < ((2 : ℝ) / 153)
  · exact interval_gap_piece_0 t hl hcut
  · have hnext : ((2 : ℝ) / 153) ≤ t := le_of_not_gt hcut
    clear hl hcut
    have hl := hnext
    clear hnext
    by_cases hcut : t < ((1 : ℝ) / 49)
    · exact interval_gap_piece_1 t hl hcut
    · have hnext : ((1 : ℝ) / 49) ≤ t := le_of_not_gt hcut
      clear hl hcut
      have hl := hnext
      clear hnext
      by_cases hcut : t < ((1 : ℝ) / 37)
      · exact interval_gap_piece_2 t hl hcut
      · have hnext : ((1 : ℝ) / 37) ≤ t := le_of_not_gt hcut
        clear hl hcut
        have hl := hnext
        clear hnext
        by_cases hcut : t < ((1 : ℝ) / 30)
        · exact interval_gap_piece_3 t hl hcut
        · have hnext : ((1 : ℝ) / 30) ≤ t := le_of_not_gt hcut
          clear hl hcut
          have hl := hnext
          clear hnext
          by_cases hcut : t < ((2 : ℝ) / 49)
          · exact interval_gap_piece_4 t hl hcut
          · have hnext : ((2 : ℝ) / 49) ≤ t := le_of_not_gt hcut
            clear hl hcut
            have hl := hnext
            clear hnext
            by_cases hcut : t < ((2 : ℝ) / 45)
            · exact interval_gap_piece_5 t hl hcut
            · have hnext : ((2 : ℝ) / 45) ≤ t := le_of_not_gt hcut
              clear hl hcut
              have hl := hnext
              clear hnext
              by_cases hcut : t < ((1 : ℝ) / 20)
              · exact interval_gap_piece_6 t hl hcut
              · have hnext : ((1 : ℝ) / 20) ≤ t := le_of_not_gt hcut
                clear hl hcut
                have hl := hnext
                clear hnext
                by_cases hcut : t < ((1 : ℝ) / 17)
                · exact interval_gap_piece_7 t hl hcut
                · have hnext : ((1 : ℝ) / 17) ≤ t := le_of_not_gt hcut
                  clear hl hcut
                  have hl := hnext
                  clear hnext
                  by_cases hcut : t < ((2 : ℝ) / 31)
                  · exact interval_gap_piece_8 t hl hcut
                  · have hnext : ((2 : ℝ) / 31) ≤ t := le_of_not_gt hcut
                    clear hl hcut
                    have hl := hnext
                    clear hnext
                    exact interval_gap_piece_9 t hl hu
