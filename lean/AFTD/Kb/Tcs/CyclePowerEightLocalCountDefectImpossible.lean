import AFTD.Prelude

/-!
# cycle_power_eight_local_count_defect_impossible

Topic: combinatorics   Node: 06b2c1ad0450

Provenance: helper lemma. Local helper for the cycle-power equivalence-covering problem.

In the length-eight Boolean rooted-class model, suppose endpoints occur, boundary bits are paired and alternate, the two indicated parent implications hold, every distance is covered, the length-four edges are covered exactly once, and the active interior counts at -1 and 0 are both one. If the boundary bit at zero is false, then the offset-three bit at zero cannot be true.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
namespace CyclePowerEightLocalCount
def rt1_one3 (a b c : Bool) : Bool :=
  (a && !b && !c) || (!a && b && !c) || (!a && !b && c)

def rt1_one4 (a b c d : Bool) : Bool :=
  (a && !b && !c && !d) || (!a && b && !c && !d) ||
  (!a && !b && c && !d) || (!a && !b && !c && d)

lrat_proof rt1_count_lrat
  "p cnf 60 101\n-1 0\n-2 0\n-3 0\n-4 0\n-5 0\n-6 0\n1 7 8 10 13 0\n7 8 10 12 13 0\n1 7 8 11 13 0\n7 8 11 12 13 0\n1 7 9 10 13 0\n7 9 10 12 13 0\n1 7 9 11 13 0\n7 9 11 12 13 0\n5 6 14 16 19 0\n6 14 16 18 19 0\n5 6 14 17 19 0\n6 14 17 18 19 0\n5 14 15 16 19 0\n14 15 16 18 19 0\n5 14 15 17 19 0\n14 15 17 18 19 0\n8 10 12 20 21 0\n10 12 20 21 22 0\n23 25 28 0\n23 26 28 0\n3 23 24 29 30 0\n23 24 29 30 31 0\n30 32 34 0\n30 32 35 0\n4 36 37 39 40 0\n36 37 38 39 40 0\n5 15 17 42 43 0\n15 17 41 42 43 0\n26 44 0\n45 46 0\n34 47 0\n48 49 0\n12 13 51 0\n-12 -13 0\n-12 -51 0\n-13 -51 0\n10 52 53 0\n-52 -53 0\n-10 -52 0\n-10 -53 0\n7 9 28 0\n-7 -28 0\n-9 -28 0\n-7 -9 0\n24 26 55 0\n-24 -26 0\n-24 -55 0\n-26 -55 0\n30 46 56 0\n-30 -46 0\n-30 -56 0\n-46 -56 0\n23 40 45 0\n-40 -45 0\n-23 -40 0\n-23 -45 0\n29 34 37 0\n-34 -37 0\n-29 -37 0\n-29 -34 0\n39 43 47 0\n-43 -47 0\n-39 -43 0\n-39 -47 0\n18 19 32 0\n-18 -19 0\n-18 -32 0\n-19 -32 0\n17 36 49 0\n-17 -49 0\n-17 -36 0\n-36 -49 0\n42 48 58 0\n-48 -58 0\n-42 -58 0\n-42 -48 0\n14 15 59 0\n-14 -59 0\n-15 -59 0\n-14 -15 0\n44 20 21 22 0\n-44 -20 0\n-44 -21 0\n-44 -22 0\n-20 -21 0\n-20 -22 0\n-21 -22 0\n2 55 52 53 0\n-2 -55 0\n-2 -52 0\n-2 -53 0\n-55 -52 0\n-55 -53 0\n-52 -53 0\n56 0\n"
  "101 d 7 8 9 10 12 13 14 15 16 18 19 20 21 22 23 25 28 30 32 34 39 41 42 43 44 47 50 51 54 55 56 59 61 63 64 67 69 71 72 73 75 76 79 80 81 83 84 85 87 91 92 93 95 96 97 98 99 100 0\n102 26 10 0 1 101 58 36 62 26 35 48 49 88 89 90 11 24 40 0\n102 d 26 35 48 49 88 89 90 11 24 40 0\n103 -29 0 4 5 6 101 57 58 36 60 65 66 37 29 68 70 74 31 77 78 17 38 86 82 33 0\n103 d 60 65 66 37 29 68 70 74 31 77 78 17 38 86 82 33 0\n105 0 2 3 101 57 58 36 62 103 27 52 53 102 45 46 94 0\n"

theorem rt1_count_defect_boolean_core (x : ℤ → ℕ → Bool)
    (hp_m8_5 : x (-8 : ℤ) 5 = false)
    (hp_m2_2 : x (-2 : ℤ) 2 = false)
    (hp_2_2 : x (2 : ℤ) 2 = false)
    (hp_6_5 : x (6 : ℤ) 5 = false)
    (hp_10_5 : x (10 : ℤ) 5 = false)
    (hp_12_2 : x (12 : ℤ) 2 = false)
    (hc_1_m4 : (((x (-5 : ℤ) 2)) || ((x (-6 : ℤ) 2) && (x (-6 : ℤ) 3)) || ((x (-7 : ℤ) 3) && (x (-7 : ℤ) 4)) || ((x (-8 : ℤ) 4) && (x (-8 : ℤ) 5)) || ((x (-9 : ℤ) 5))) = true)
    (hc_1_14 : (((x (13 : ℤ) 2)) || ((x (12 : ℤ) 2) && (x (12 : ℤ) 3)) || ((x (11 : ℤ) 3) && (x (11 : ℤ) 4)) || ((x (10 : ℤ) 4) && (x (10 : ℤ) 5)) || ((x (9 : ℤ) 5))) = true)
    (hc_3_m4 : (((x (-4 : ℤ) 3)) || ((x (-5 : ℤ) 4)) || ((x (-6 : ℤ) 2) && (x (-6 : ℤ) 5)) || ((x (-7 : ℤ) 3)) || ((x (-8 : ℤ) 4))) = true)
    (hc_3_1 : (((x (1 : ℤ) 3)) || ((x (-1 : ℤ) 2) && (x (-1 : ℤ) 5)) || ((x (-3 : ℤ) 4))) = true)
    (hc_3_4 : (((x (4 : ℤ) 3)) || ((x (3 : ℤ) 4)) || ((x (2 : ℤ) 2) && (x (2 : ℤ) 5)) || ((x (1 : ℤ) 3)) || ((x (0 : ℤ) 4))) = true)
    (hc_3_7 : (((x (7 : ℤ) 3)) || ((x (5 : ℤ) 2) && (x (5 : ℤ) 5)) || ((x (3 : ℤ) 4))) = true)
    (hc_3_8 : (((x (8 : ℤ) 3)) || ((x (7 : ℤ) 4)) || ((x (6 : ℤ) 2) && (x (6 : ℤ) 5)) || ((x (5 : ℤ) 3)) || ((x (4 : ℤ) 4))) = true)
    (hc_3_12 : (((x (12 : ℤ) 3)) || ((x (11 : ℤ) 4)) || ((x (10 : ℤ) 2) && (x (10 : ℤ) 5)) || ((x (9 : ℤ) 3)) || ((x (8 : ℤ) 4))) = true)
    (hc_5_m1 : (((x (-1 : ℤ) 5)) || ((x (-3 : ℤ) 2))) = true)
    (hc_5_3 : (((x (3 : ℤ) 5)) || ((x (1 : ℤ) 2))) = true)
    (hc_5_7 : (((x (7 : ℤ) 5)) || ((x (5 : ℤ) 2))) = true)
    (hc_5_11 : (((x (11 : ℤ) 5)) || ((x (9 : ℤ) 2))) = true)
    (he_m8 : rt1_one3 (x (-8 : ℤ) 4) (x (-9 : ℤ) 5) (x (-11 : ℤ) 3) = true)
    (he_m4 : rt1_one3 (x (-4 : ℤ) 4) (x (-5 : ℤ) 5) (x (-7 : ℤ) 3) = true)
    (he_m3 : rt1_one3 (x (-3 : ℤ) 4) (x (-5 : ℤ) 2) (x (-6 : ℤ) 3) = true)
    (he_0 : rt1_one3 (x (0 : ℤ) 4) (x (-1 : ℤ) 5) (x (-3 : ℤ) 3) = true)
    (he_3 : rt1_one3 (x (3 : ℤ) 4) (x (1 : ℤ) 2) (x (0 : ℤ) 3) = true)
    (he_4 : rt1_one3 (x (4 : ℤ) 4) (x (3 : ℤ) 5) (x (1 : ℤ) 3) = true)
    (he_7 : rt1_one3 (x (7 : ℤ) 4) (x (5 : ℤ) 2) (x (4 : ℤ) 3) = true)
    (he_8 : rt1_one3 (x (8 : ℤ) 4) (x (7 : ℤ) 5) (x (5 : ℤ) 3) = true)
    (he_10 : rt1_one3 (x (10 : ℤ) 4) (x (9 : ℤ) 5) (x (7 : ℤ) 3) = true)
    (he_11 : rt1_one3 (x (11 : ℤ) 4) (x (9 : ℤ) 2) (x (8 : ℤ) 3) = true)
    (he_12 : rt1_one3 (x (12 : ℤ) 4) (x (11 : ℤ) 5) (x (9 : ℤ) 3) = true)
    (he_15 : rt1_one3 (x (15 : ℤ) 4) (x (13 : ℤ) 2) (x (12 : ℤ) 3) = true)
    (hn_m1 : rt1_one4 (x (-3 : ℤ) 2) (x (-4 : ℤ) 3) (x (-5 : ℤ) 4) (x (-6 : ℤ) 5) = true)
    (hn_0 : rt1_one4 (x (-2 : ℤ) 2) (x (-3 : ℤ) 3) (x (-4 : ℤ) 4) (x (-5 : ℤ) 5) = true)
    (hdefect : x (0 : ℤ) 3 = true) : False := by
  classical
  have hcl0 : ¬ ((x (-8 : ℤ) 5 = true)) := by
    have h := hp_m8_5
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl1 : ¬ ((x (-2 : ℤ) 2 = true)) := by
    have h := hp_m2_2
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl2 : ¬ ((x (2 : ℤ) 2 = true)) := by
    have h := hp_2_2
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl3 : ¬ ((x (6 : ℤ) 5 = true)) := by
    have h := hp_6_5
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl4 : ¬ ((x (10 : ℤ) 5 = true)) := by
    have h := hp_10_5
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl5 : ¬ ((x (12 : ℤ) 2 = true)) := by
    have h := hp_12_2
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl6 : ¬ (¬ (x (-8 : ℤ) 5 = true) ∧ ¬ (x (-5 : ℤ) 2 = true) ∧ ¬ (x (-6 : ℤ) 2 = true) ∧ ¬ (x (-7 : ℤ) 3 = true) ∧ ¬ (x (-9 : ℤ) 5 = true)) := by
    have h := hc_1_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl7 : ¬ (¬ (x (-5 : ℤ) 2 = true) ∧ ¬ (x (-6 : ℤ) 2 = true) ∧ ¬ (x (-7 : ℤ) 3 = true) ∧ ¬ (x (-8 : ℤ) 4 = true) ∧ ¬ (x (-9 : ℤ) 5 = true)) := by
    have h := hc_1_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl8 : ¬ (¬ (x (-8 : ℤ) 5 = true) ∧ ¬ (x (-5 : ℤ) 2 = true) ∧ ¬ (x (-6 : ℤ) 2 = true) ∧ ¬ (x (-7 : ℤ) 4 = true) ∧ ¬ (x (-9 : ℤ) 5 = true)) := by
    have h := hc_1_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl9 : ¬ (¬ (x (-5 : ℤ) 2 = true) ∧ ¬ (x (-6 : ℤ) 2 = true) ∧ ¬ (x (-7 : ℤ) 4 = true) ∧ ¬ (x (-8 : ℤ) 4 = true) ∧ ¬ (x (-9 : ℤ) 5 = true)) := by
    have h := hc_1_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl10 : ¬ (¬ (x (-8 : ℤ) 5 = true) ∧ ¬ (x (-5 : ℤ) 2 = true) ∧ ¬ (x (-6 : ℤ) 3 = true) ∧ ¬ (x (-7 : ℤ) 3 = true) ∧ ¬ (x (-9 : ℤ) 5 = true)) := by
    have h := hc_1_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl11 : ¬ (¬ (x (-5 : ℤ) 2 = true) ∧ ¬ (x (-6 : ℤ) 3 = true) ∧ ¬ (x (-7 : ℤ) 3 = true) ∧ ¬ (x (-8 : ℤ) 4 = true) ∧ ¬ (x (-9 : ℤ) 5 = true)) := by
    have h := hc_1_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl12 : ¬ (¬ (x (-8 : ℤ) 5 = true) ∧ ¬ (x (-5 : ℤ) 2 = true) ∧ ¬ (x (-6 : ℤ) 3 = true) ∧ ¬ (x (-7 : ℤ) 4 = true) ∧ ¬ (x (-9 : ℤ) 5 = true)) := by
    have h := hc_1_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl13 : ¬ (¬ (x (-5 : ℤ) 2 = true) ∧ ¬ (x (-6 : ℤ) 3 = true) ∧ ¬ (x (-7 : ℤ) 4 = true) ∧ ¬ (x (-8 : ℤ) 4 = true) ∧ ¬ (x (-9 : ℤ) 5 = true)) := by
    have h := hc_1_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl14 : ¬ (¬ (x (10 : ℤ) 5 = true) ∧ ¬ (x (12 : ℤ) 2 = true) ∧ ¬ (x (13 : ℤ) 2 = true) ∧ ¬ (x (11 : ℤ) 3 = true) ∧ ¬ (x (9 : ℤ) 5 = true)) := by
    have h := hc_1_14
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl15 : ¬ (¬ (x (12 : ℤ) 2 = true) ∧ ¬ (x (13 : ℤ) 2 = true) ∧ ¬ (x (11 : ℤ) 3 = true) ∧ ¬ (x (10 : ℤ) 4 = true) ∧ ¬ (x (9 : ℤ) 5 = true)) := by
    have h := hc_1_14
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl16 : ¬ (¬ (x (10 : ℤ) 5 = true) ∧ ¬ (x (12 : ℤ) 2 = true) ∧ ¬ (x (13 : ℤ) 2 = true) ∧ ¬ (x (11 : ℤ) 4 = true) ∧ ¬ (x (9 : ℤ) 5 = true)) := by
    have h := hc_1_14
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl17 : ¬ (¬ (x (12 : ℤ) 2 = true) ∧ ¬ (x (13 : ℤ) 2 = true) ∧ ¬ (x (11 : ℤ) 4 = true) ∧ ¬ (x (10 : ℤ) 4 = true) ∧ ¬ (x (9 : ℤ) 5 = true)) := by
    have h := hc_1_14
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl18 : ¬ (¬ (x (10 : ℤ) 5 = true) ∧ ¬ (x (13 : ℤ) 2 = true) ∧ ¬ (x (12 : ℤ) 3 = true) ∧ ¬ (x (11 : ℤ) 3 = true) ∧ ¬ (x (9 : ℤ) 5 = true)) := by
    have h := hc_1_14
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl19 : ¬ (¬ (x (13 : ℤ) 2 = true) ∧ ¬ (x (12 : ℤ) 3 = true) ∧ ¬ (x (11 : ℤ) 3 = true) ∧ ¬ (x (10 : ℤ) 4 = true) ∧ ¬ (x (9 : ℤ) 5 = true)) := by
    have h := hc_1_14
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl20 : ¬ (¬ (x (10 : ℤ) 5 = true) ∧ ¬ (x (13 : ℤ) 2 = true) ∧ ¬ (x (12 : ℤ) 3 = true) ∧ ¬ (x (11 : ℤ) 4 = true) ∧ ¬ (x (9 : ℤ) 5 = true)) := by
    have h := hc_1_14
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl21 : ¬ (¬ (x (13 : ℤ) 2 = true) ∧ ¬ (x (12 : ℤ) 3 = true) ∧ ¬ (x (11 : ℤ) 4 = true) ∧ ¬ (x (10 : ℤ) 4 = true) ∧ ¬ (x (9 : ℤ) 5 = true)) := by
    have h := hc_1_14
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl22 : ¬ (¬ (x (-6 : ℤ) 2 = true) ∧ ¬ (x (-7 : ℤ) 3 = true) ∧ ¬ (x (-8 : ℤ) 4 = true) ∧ ¬ (x (-4 : ℤ) 3 = true) ∧ ¬ (x (-5 : ℤ) 4 = true)) := by
    have h := hc_3_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl23 : ¬ (¬ (x (-7 : ℤ) 3 = true) ∧ ¬ (x (-8 : ℤ) 4 = true) ∧ ¬ (x (-4 : ℤ) 3 = true) ∧ ¬ (x (-5 : ℤ) 4 = true) ∧ ¬ (x (-6 : ℤ) 5 = true)) := by
    have h := hc_3_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl24 : ¬ (¬ (x (1 : ℤ) 3 = true) ∧ ¬ (x (-1 : ℤ) 2 = true) ∧ ¬ (x (-3 : ℤ) 4 = true)) := by
    have h := hc_3_1
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl25 : ¬ (¬ (x (1 : ℤ) 3 = true) ∧ ¬ (x (-1 : ℤ) 5 = true) ∧ ¬ (x (-3 : ℤ) 4 = true)) := by
    have h := hc_3_1
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl26 : ¬ (¬ (x (2 : ℤ) 2 = true) ∧ ¬ (x (1 : ℤ) 3 = true) ∧ ¬ (x (0 : ℤ) 4 = true) ∧ ¬ (x (4 : ℤ) 3 = true) ∧ ¬ (x (3 : ℤ) 4 = true)) := by
    have h := hc_3_4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl27 : ¬ (¬ (x (1 : ℤ) 3 = true) ∧ ¬ (x (0 : ℤ) 4 = true) ∧ ¬ (x (4 : ℤ) 3 = true) ∧ ¬ (x (3 : ℤ) 4 = true) ∧ ¬ (x (2 : ℤ) 5 = true)) := by
    have h := hc_3_4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl28 : ¬ (¬ (x (3 : ℤ) 4 = true) ∧ ¬ (x (7 : ℤ) 3 = true) ∧ ¬ (x (5 : ℤ) 2 = true)) := by
    have h := hc_3_7
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl29 : ¬ (¬ (x (3 : ℤ) 4 = true) ∧ ¬ (x (7 : ℤ) 3 = true) ∧ ¬ (x (5 : ℤ) 5 = true)) := by
    have h := hc_3_7
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl30 : ¬ (¬ (x (6 : ℤ) 5 = true) ∧ ¬ (x (8 : ℤ) 3 = true) ∧ ¬ (x (7 : ℤ) 4 = true) ∧ ¬ (x (5 : ℤ) 3 = true) ∧ ¬ (x (4 : ℤ) 4 = true)) := by
    have h := hc_3_8
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl31 : ¬ (¬ (x (8 : ℤ) 3 = true) ∧ ¬ (x (7 : ℤ) 4 = true) ∧ ¬ (x (6 : ℤ) 2 = true) ∧ ¬ (x (5 : ℤ) 3 = true) ∧ ¬ (x (4 : ℤ) 4 = true)) := by
    have h := hc_3_8
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl32 : ¬ (¬ (x (10 : ℤ) 5 = true) ∧ ¬ (x (12 : ℤ) 3 = true) ∧ ¬ (x (11 : ℤ) 4 = true) ∧ ¬ (x (9 : ℤ) 3 = true) ∧ ¬ (x (8 : ℤ) 4 = true)) := by
    have h := hc_3_12
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl33 : ¬ (¬ (x (12 : ℤ) 3 = true) ∧ ¬ (x (11 : ℤ) 4 = true) ∧ ¬ (x (10 : ℤ) 2 = true) ∧ ¬ (x (9 : ℤ) 3 = true) ∧ ¬ (x (8 : ℤ) 4 = true)) := by
    have h := hc_3_12
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl34 : ¬ (¬ (x (-1 : ℤ) 5 = true) ∧ ¬ (x (-3 : ℤ) 2 = true)) := by
    have h := hc_5_m1
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl35 : ¬ (¬ (x (3 : ℤ) 5 = true) ∧ ¬ (x (1 : ℤ) 2 = true)) := by
    have h := hc_5_3
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl36 : ¬ (¬ (x (5 : ℤ) 2 = true) ∧ ¬ (x (7 : ℤ) 5 = true)) := by
    have h := hc_5_7
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl37 : ¬ (¬ (x (11 : ℤ) 5 = true) ∧ ¬ (x (9 : ℤ) 2 = true)) := by
    have h := hc_5_11
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl38 : ¬ (¬ (x (-8 : ℤ) 4 = true) ∧ ¬ (x (-9 : ℤ) 5 = true) ∧ ¬ (x (-11 : ℤ) 3 = true)) := by
    have h := he_m8
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl39 : ¬ ((x (-8 : ℤ) 4 = true) ∧ (x (-9 : ℤ) 5 = true)) := by
    have h := he_m8
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl40 : ¬ ((x (-8 : ℤ) 4 = true) ∧ (x (-11 : ℤ) 3 = true)) := by
    have h := he_m8
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl41 : ¬ ((x (-9 : ℤ) 5 = true) ∧ (x (-11 : ℤ) 3 = true)) := by
    have h := he_m8
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl42 : ¬ (¬ (x (-7 : ℤ) 3 = true) ∧ ¬ (x (-4 : ℤ) 4 = true) ∧ ¬ (x (-5 : ℤ) 5 = true)) := by
    have h := he_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl43 : ¬ ((x (-4 : ℤ) 4 = true) ∧ (x (-5 : ℤ) 5 = true)) := by
    have h := he_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl44 : ¬ ((x (-7 : ℤ) 3 = true) ∧ (x (-4 : ℤ) 4 = true)) := by
    have h := he_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl45 : ¬ ((x (-7 : ℤ) 3 = true) ∧ (x (-5 : ℤ) 5 = true)) := by
    have h := he_m4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl46 : ¬ (¬ (x (-5 : ℤ) 2 = true) ∧ ¬ (x (-6 : ℤ) 3 = true) ∧ ¬ (x (-3 : ℤ) 4 = true)) := by
    have h := he_m3
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl47 : ¬ ((x (-5 : ℤ) 2 = true) ∧ (x (-3 : ℤ) 4 = true)) := by
    have h := he_m3
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl48 : ¬ ((x (-6 : ℤ) 3 = true) ∧ (x (-3 : ℤ) 4 = true)) := by
    have h := he_m3
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl49 : ¬ ((x (-5 : ℤ) 2 = true) ∧ (x (-6 : ℤ) 3 = true)) := by
    have h := he_m3
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl50 : ¬ (¬ (x (0 : ℤ) 4 = true) ∧ ¬ (x (-1 : ℤ) 5 = true) ∧ ¬ (x (-3 : ℤ) 3 = true)) := by
    have h := he_0
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl51 : ¬ ((x (0 : ℤ) 4 = true) ∧ (x (-1 : ℤ) 5 = true)) := by
    have h := he_0
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl52 : ¬ ((x (0 : ℤ) 4 = true) ∧ (x (-3 : ℤ) 3 = true)) := by
    have h := he_0
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl53 : ¬ ((x (-1 : ℤ) 5 = true) ∧ (x (-3 : ℤ) 3 = true)) := by
    have h := he_0
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl54 : ¬ (¬ (x (3 : ℤ) 4 = true) ∧ ¬ (x (1 : ℤ) 2 = true) ∧ ¬ (x (0 : ℤ) 3 = true)) := by
    have h := he_3
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl55 : ¬ ((x (3 : ℤ) 4 = true) ∧ (x (1 : ℤ) 2 = true)) := by
    have h := he_3
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl56 : ¬ ((x (3 : ℤ) 4 = true) ∧ (x (0 : ℤ) 3 = true)) := by
    have h := he_3
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl57 : ¬ ((x (1 : ℤ) 2 = true) ∧ (x (0 : ℤ) 3 = true)) := by
    have h := he_3
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl58 : ¬ (¬ (x (1 : ℤ) 3 = true) ∧ ¬ (x (4 : ℤ) 4 = true) ∧ ¬ (x (3 : ℤ) 5 = true)) := by
    have h := he_4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl59 : ¬ ((x (4 : ℤ) 4 = true) ∧ (x (3 : ℤ) 5 = true)) := by
    have h := he_4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl60 : ¬ ((x (1 : ℤ) 3 = true) ∧ (x (4 : ℤ) 4 = true)) := by
    have h := he_4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl61 : ¬ ((x (1 : ℤ) 3 = true) ∧ (x (3 : ℤ) 5 = true)) := by
    have h := he_4
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl62 : ¬ (¬ (x (4 : ℤ) 3 = true) ∧ ¬ (x (5 : ℤ) 2 = true) ∧ ¬ (x (7 : ℤ) 4 = true)) := by
    have h := he_7
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl63 : ¬ ((x (5 : ℤ) 2 = true) ∧ (x (7 : ℤ) 4 = true)) := by
    have h := he_7
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl64 : ¬ ((x (4 : ℤ) 3 = true) ∧ (x (7 : ℤ) 4 = true)) := by
    have h := he_7
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl65 : ¬ ((x (4 : ℤ) 3 = true) ∧ (x (5 : ℤ) 2 = true)) := by
    have h := he_7
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl66 : ¬ (¬ (x (5 : ℤ) 3 = true) ∧ ¬ (x (8 : ℤ) 4 = true) ∧ ¬ (x (7 : ℤ) 5 = true)) := by
    have h := he_8
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl67 : ¬ ((x (8 : ℤ) 4 = true) ∧ (x (7 : ℤ) 5 = true)) := by
    have h := he_8
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl68 : ¬ ((x (5 : ℤ) 3 = true) ∧ (x (8 : ℤ) 4 = true)) := by
    have h := he_8
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl69 : ¬ ((x (5 : ℤ) 3 = true) ∧ (x (7 : ℤ) 5 = true)) := by
    have h := he_8
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl70 : ¬ (¬ (x (10 : ℤ) 4 = true) ∧ ¬ (x (9 : ℤ) 5 = true) ∧ ¬ (x (7 : ℤ) 3 = true)) := by
    have h := he_10
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl71 : ¬ ((x (10 : ℤ) 4 = true) ∧ (x (9 : ℤ) 5 = true)) := by
    have h := he_10
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl72 : ¬ ((x (10 : ℤ) 4 = true) ∧ (x (7 : ℤ) 3 = true)) := by
    have h := he_10
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl73 : ¬ ((x (9 : ℤ) 5 = true) ∧ (x (7 : ℤ) 3 = true)) := by
    have h := he_10
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl74 : ¬ (¬ (x (11 : ℤ) 4 = true) ∧ ¬ (x (8 : ℤ) 3 = true) ∧ ¬ (x (9 : ℤ) 2 = true)) := by
    have h := he_11
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl75 : ¬ ((x (11 : ℤ) 4 = true) ∧ (x (9 : ℤ) 2 = true)) := by
    have h := he_11
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl76 : ¬ ((x (11 : ℤ) 4 = true) ∧ (x (8 : ℤ) 3 = true)) := by
    have h := he_11
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl77 : ¬ ((x (8 : ℤ) 3 = true) ∧ (x (9 : ℤ) 2 = true)) := by
    have h := he_11
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl78 : ¬ (¬ (x (9 : ℤ) 3 = true) ∧ ¬ (x (11 : ℤ) 5 = true) ∧ ¬ (x (12 : ℤ) 4 = true)) := by
    have h := he_12
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl79 : ¬ ((x (11 : ℤ) 5 = true) ∧ (x (12 : ℤ) 4 = true)) := by
    have h := he_12
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl80 : ¬ ((x (9 : ℤ) 3 = true) ∧ (x (12 : ℤ) 4 = true)) := by
    have h := he_12
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl81 : ¬ ((x (9 : ℤ) 3 = true) ∧ (x (11 : ℤ) 5 = true)) := by
    have h := he_12
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl82 : ¬ (¬ (x (13 : ℤ) 2 = true) ∧ ¬ (x (12 : ℤ) 3 = true) ∧ ¬ (x (15 : ℤ) 4 = true)) := by
    have h := he_15
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl83 : ¬ ((x (13 : ℤ) 2 = true) ∧ (x (15 : ℤ) 4 = true)) := by
    have h := he_15
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl84 : ¬ ((x (12 : ℤ) 3 = true) ∧ (x (15 : ℤ) 4 = true)) := by
    have h := he_15
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl85 : ¬ ((x (13 : ℤ) 2 = true) ∧ (x (12 : ℤ) 3 = true)) := by
    have h := he_15
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl86 : ¬ (¬ (x (-3 : ℤ) 2 = true) ∧ ¬ (x (-4 : ℤ) 3 = true) ∧ ¬ (x (-5 : ℤ) 4 = true) ∧ ¬ (x (-6 : ℤ) 5 = true)) := by
    have h := hn_m1
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl87 : ¬ ((x (-3 : ℤ) 2 = true) ∧ (x (-4 : ℤ) 3 = true)) := by
    have h := hn_m1
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl88 : ¬ ((x (-3 : ℤ) 2 = true) ∧ (x (-5 : ℤ) 4 = true)) := by
    have h := hn_m1
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl89 : ¬ ((x (-3 : ℤ) 2 = true) ∧ (x (-6 : ℤ) 5 = true)) := by
    have h := hn_m1
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl90 : ¬ ((x (-4 : ℤ) 3 = true) ∧ (x (-5 : ℤ) 4 = true)) := by
    have h := hn_m1
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl91 : ¬ ((x (-4 : ℤ) 3 = true) ∧ (x (-6 : ℤ) 5 = true)) := by
    have h := hn_m1
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl92 : ¬ ((x (-5 : ℤ) 4 = true) ∧ (x (-6 : ℤ) 5 = true)) := by
    have h := hn_m1
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl93 : ¬ (¬ (x (-2 : ℤ) 2 = true) ∧ ¬ (x (-3 : ℤ) 3 = true) ∧ ¬ (x (-4 : ℤ) 4 = true) ∧ ¬ (x (-5 : ℤ) 5 = true)) := by
    have h := hn_0
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl94 : ¬ ((x (-2 : ℤ) 2 = true) ∧ (x (-3 : ℤ) 3 = true)) := by
    have h := hn_0
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl95 : ¬ ((x (-2 : ℤ) 2 = true) ∧ (x (-4 : ℤ) 4 = true)) := by
    have h := hn_0
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl96 : ¬ ((x (-2 : ℤ) 2 = true) ∧ (x (-5 : ℤ) 5 = true)) := by
    have h := hn_0
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl97 : ¬ ((x (-3 : ℤ) 3 = true) ∧ (x (-4 : ℤ) 4 = true)) := by
    have h := hn_0
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl98 : ¬ ((x (-3 : ℤ) 3 = true) ∧ (x (-5 : ℤ) 5 = true)) := by
    have h := hn_0
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl99 : ¬ ((x (-4 : ℤ) 4 = true) ∧ (x (-5 : ℤ) 5 = true)) := by
    have h := hn_0
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have hcl100 : ¬ (¬ (x (0 : ℤ) 3 = true)) := by
    have h := hdefect
    clear * - h
    try simp only [rt1_one3, rt1_one4, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    try simp only [Bool.eq_false_iff] at *
    tauto
  have bad := rt1_count_lrat (x (-8 : ℤ) 5 = true) (x (-2 : ℤ) 2 = true) (x (2 : ℤ) 2 = true) (x (6 : ℤ) 5 = true) (x (10 : ℤ) 5 = true) (x (12 : ℤ) 2 = true) (x (-5 : ℤ) 2 = true) (x (-6 : ℤ) 2 = true) (x (-6 : ℤ) 3 = true) (x (-7 : ℤ) 3 = true) (x (-7 : ℤ) 4 = true) (x (-8 : ℤ) 4 = true) (x (-9 : ℤ) 5 = true) (x (13 : ℤ) 2 = true) (x (12 : ℤ) 3 = true) (x (11 : ℤ) 3 = true) (x (11 : ℤ) 4 = true) (x (10 : ℤ) 4 = true) (x (9 : ℤ) 5 = true) (x (-4 : ℤ) 3 = true) (x (-5 : ℤ) 4 = true) (x (-6 : ℤ) 5 = true) (x (1 : ℤ) 3 = true) (x (0 : ℤ) 4 = true) (x (-1 : ℤ) 2 = true) (x (-1 : ℤ) 5 = true) (x (-2 : ℤ) 3 = true) (x (-3 : ℤ) 4 = true) (x (4 : ℤ) 3 = true) (x (3 : ℤ) 4 = true) (x (2 : ℤ) 5 = true) (x (7 : ℤ) 3 = true) (x (6 : ℤ) 4 = true) (x (5 : ℤ) 2 = true) (x (5 : ℤ) 5 = true) (x (8 : ℤ) 3 = true) (x (7 : ℤ) 4 = true) (x (6 : ℤ) 2 = true) (x (5 : ℤ) 3 = true) (x (4 : ℤ) 4 = true) (x (10 : ℤ) 2 = true) (x (9 : ℤ) 3 = true) (x (8 : ℤ) 4 = true) (x (-3 : ℤ) 2 = true) (x (3 : ℤ) 5 = true) (x (1 : ℤ) 2 = true) (x (7 : ℤ) 5 = true) (x (11 : ℤ) 5 = true) (x (9 : ℤ) 2 = true) (x (-10 : ℤ) 2 = true) (x (-11 : ℤ) 3 = true) (x (-4 : ℤ) 4 = true) (x (-5 : ℤ) 5 = true) (x (-4 : ℤ) 5 = true) (x (-3 : ℤ) 3 = true) (x (0 : ℤ) 3 = true) (x (8 : ℤ) 2 = true) (x (12 : ℤ) 4 = true) (x (15 : ℤ) 4 = true) (x (14 : ℤ) 5 = true)
  repeat' first | contradiction | rcases bad with bad | bad

end CyclePowerEightLocalCount
open CyclePowerEightLocalCount
open Finset

theorem cycle_power_eight_local_count_defect_impossible
    (x : ℤ → ℕ → Bool)
    (hends0 : ∀ v, x v 0 = true)
    (hends7 : ∀ v, x v 7 = true)
    (hpair : ∀ v, x v 6 = x v 1)
    (halt : ∀ v, x (v+1) 1 = !x v 1)
    (hp2 : ∀ v, x v 2 = true → x v 6 = true)
    (hp5 : ∀ v, x v 5 = true → x v 1 = true)
    (hcover : ∀ d, 1 ≤ d → d < 8 → ∀ v : ℤ,
      ∃ a : ℕ, a < 8-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true)
    (hexact : ∀ v : ℤ, (range 4).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+4)).toNat) = 1)
    (hcount : ∀ v : ℤ, v = -1 ∨ v = 0 →
      (x (v-2) 2).toNat + (x (v-3) 3).toNat +
      (x (v-4) 4).toNat + (x (v-5) 5).toNat = 1)
    (hb0 : x 0 1 = false) (hdefect : x 0 3 = true) : False := by
  classical
  have hb1 : x (1 : ℤ) 1 = true := by
    have h := halt (0 : ℤ)
    norm_num at h
    simpa [hb0] using h
  have hb2 : x (2 : ℤ) 1 = false := by
    have h := halt (1 : ℤ)
    norm_num at h
    simpa [hb1] using h
  have hb3 : x (3 : ℤ) 1 = true := by
    have h := halt (2 : ℤ)
    norm_num at h
    simpa [hb2] using h
  have hb4 : x (4 : ℤ) 1 = false := by
    have h := halt (3 : ℤ)
    norm_num at h
    simpa [hb3] using h
  have hb5 : x (5 : ℤ) 1 = true := by
    have h := halt (4 : ℤ)
    norm_num at h
    simpa [hb4] using h
  have hb6 : x (6 : ℤ) 1 = false := by
    have h := halt (5 : ℤ)
    norm_num at h
    simpa [hb5] using h
  have hb7 : x (7 : ℤ) 1 = true := by
    have h := halt (6 : ℤ)
    norm_num at h
    simpa [hb6] using h
  have hb8 : x (8 : ℤ) 1 = false := by
    have h := halt (7 : ℤ)
    norm_num at h
    simpa [hb7] using h
  have hb9 : x (9 : ℤ) 1 = true := by
    have h := halt (8 : ℤ)
    norm_num at h
    simpa [hb8] using h
  have hb10 : x (10 : ℤ) 1 = false := by
    have h := halt (9 : ℤ)
    norm_num at h
    simpa [hb9] using h
  have hb11 : x (11 : ℤ) 1 = true := by
    have h := halt (10 : ℤ)
    norm_num at h
    simpa [hb10] using h
  have hb12 : x (12 : ℤ) 1 = false := by
    have h := halt (11 : ℤ)
    norm_num at h
    simpa [hb11] using h
  have hb13 : x (13 : ℤ) 1 = true := by
    have h := halt (12 : ℤ)
    norm_num at h
    simpa [hb12] using h
  have hb14 : x (14 : ℤ) 1 = false := by
    have h := halt (13 : ℤ)
    norm_num at h
    simpa [hb13] using h
  have hb15 : x (15 : ℤ) 1 = true := by
    have h := halt (14 : ℤ)
    norm_num at h
    simpa [hb14] using h
  have hb16 : x (16 : ℤ) 1 = false := by
    have h := halt (15 : ℤ)
    norm_num at h
    simpa [hb15] using h
  have hbm1 : x (-1 : ℤ) 1 = true := by
    have h := halt (-1 : ℤ)
    norm_num at h
    rw [hb0] at h
    cases hv : x (-1 : ℤ) 1 <;> simp [hv] at h ⊢
  have hbm2 : x (-2 : ℤ) 1 = false := by
    have h := halt (-2 : ℤ)
    norm_num at h
    rw [hbm1] at h
    cases hv : x (-2 : ℤ) 1 <;> simp [hv] at h ⊢
  have hbm3 : x (-3 : ℤ) 1 = true := by
    have h := halt (-3 : ℤ)
    norm_num at h
    rw [hbm2] at h
    cases hv : x (-3 : ℤ) 1 <;> simp [hv] at h ⊢
  have hbm4 : x (-4 : ℤ) 1 = false := by
    have h := halt (-4 : ℤ)
    norm_num at h
    rw [hbm3] at h
    cases hv : x (-4 : ℤ) 1 <;> simp [hv] at h ⊢
  have hbm5 : x (-5 : ℤ) 1 = true := by
    have h := halt (-5 : ℤ)
    norm_num at h
    rw [hbm4] at h
    cases hv : x (-5 : ℤ) 1 <;> simp [hv] at h ⊢
  have hbm6 : x (-6 : ℤ) 1 = false := by
    have h := halt (-6 : ℤ)
    norm_num at h
    rw [hbm5] at h
    cases hv : x (-6 : ℤ) 1 <;> simp [hv] at h ⊢
  have hbm7 : x (-7 : ℤ) 1 = true := by
    have h := halt (-7 : ℤ)
    norm_num at h
    rw [hbm6] at h
    cases hv : x (-7 : ℤ) 1 <;> simp [hv] at h ⊢
  have hbm8 : x (-8 : ℤ) 1 = false := by
    have h := halt (-8 : ℤ)
    norm_num at h
    rw [hbm7] at h
    cases hv : x (-8 : ℤ) 1 <;> simp [hv] at h ⊢
  have hbm9 : x (-9 : ℤ) 1 = true := by
    have h := halt (-9 : ℤ)
    norm_num at h
    rw [hbm8] at h
    cases hv : x (-9 : ℤ) 1 <;> simp [hv] at h ⊢
  have hbm10 : x (-10 : ℤ) 1 = false := by
    have h := halt (-10 : ℤ)
    norm_num at h
    rw [hbm9] at h
    cases hv : x (-10 : ℤ) 1 <;> simp [hv] at h ⊢
  have hbm11 : x (-11 : ℤ) 1 = true := by
    have h := halt (-11 : ℤ)
    norm_num at h
    rw [hbm10] at h
    cases hv : x (-11 : ℤ) 1 <;> simp [hv] at h ⊢
  have hbm12 : x (-12 : ℤ) 1 = false := by
    have h := halt (-12 : ℤ)
    norm_num at h
    rw [hbm11] at h
    cases hv : x (-12 : ℤ) 1 <;> simp [hv] at h ⊢
  have hcm12 : x (-12 : ℤ) 6 = false := by rw [hpair, hbm12]
  have hcm11 : x (-11 : ℤ) 6 = true := by rw [hpair, hbm11]
  have hcm10 : x (-10 : ℤ) 6 = false := by rw [hpair, hbm10]
  have hcm9 : x (-9 : ℤ) 6 = true := by rw [hpair, hbm9]
  have hcm8 : x (-8 : ℤ) 6 = false := by rw [hpair, hbm8]
  have hcm7 : x (-7 : ℤ) 6 = true := by rw [hpair, hbm7]
  have hcm6 : x (-6 : ℤ) 6 = false := by rw [hpair, hbm6]
  have hcm5 : x (-5 : ℤ) 6 = true := by rw [hpair, hbm5]
  have hcm4 : x (-4 : ℤ) 6 = false := by rw [hpair, hbm4]
  have hcm3 : x (-3 : ℤ) 6 = true := by rw [hpair, hbm3]
  have hcm2 : x (-2 : ℤ) 6 = false := by rw [hpair, hbm2]
  have hcm1 : x (-1 : ℤ) 6 = true := by rw [hpair, hbm1]
  have hc0 : x (0 : ℤ) 6 = false := by rw [hpair, hb0]
  have hc1 : x (1 : ℤ) 6 = true := by rw [hpair, hb1]
  have hc2 : x (2 : ℤ) 6 = false := by rw [hpair, hb2]
  have hc3 : x (3 : ℤ) 6 = true := by rw [hpair, hb3]
  have hc4 : x (4 : ℤ) 6 = false := by rw [hpair, hb4]
  have hc5 : x (5 : ℤ) 6 = true := by rw [hpair, hb5]
  have hc6 : x (6 : ℤ) 6 = false := by rw [hpair, hb6]
  have hc7 : x (7 : ℤ) 6 = true := by rw [hpair, hb7]
  have hc8 : x (8 : ℤ) 6 = false := by rw [hpair, hb8]
  have hc9 : x (9 : ℤ) 6 = true := by rw [hpair, hb9]
  have hc10 : x (10 : ℤ) 6 = false := by rw [hpair, hb10]
  have hc11 : x (11 : ℤ) 6 = true := by rw [hpair, hb11]
  have hc12 : x (12 : ℤ) 6 = false := by rw [hpair, hb12]
  have hc13 : x (13 : ℤ) 6 = true := by rw [hpair, hb13]
  have hc14 : x (14 : ℤ) 6 = false := by rw [hpair, hb14]
  have hc15 : x (15 : ℤ) 6 = true := by rw [hpair, hb15]
  have hc16 : x (16 : ℤ) 6 = false := by rw [hpair, hb16]
  have hp_m8_5 : x (-8 : ℤ) 5 = false := by
    cases hv : x (-8 : ℤ) 5
    · rfl
    · have h := hp5 (-8 : ℤ) hv
      rw [hbm8] at h
      contradiction
  have hp_m2_2 : x (-2 : ℤ) 2 = false := by
    cases hv : x (-2 : ℤ) 2
    · rfl
    · have h := hp2 (-2 : ℤ) hv
      rw [hcm2] at h
      contradiction
  have hp_2_2 : x (2 : ℤ) 2 = false := by
    cases hv : x (2 : ℤ) 2
    · rfl
    · have h := hp2 (2 : ℤ) hv
      rw [hc2] at h
      contradiction
  have hp_6_5 : x (6 : ℤ) 5 = false := by
    cases hv : x (6 : ℤ) 5
    · rfl
    · have h := hp5 (6 : ℤ) hv
      rw [hb6] at h
      contradiction
  have hp_10_5 : x (10 : ℤ) 5 = false := by
    cases hv : x (10 : ℤ) 5
    · rfl
    · have h := hp5 (10 : ℤ) hv
      rw [hb10] at h
      contradiction
  have hp_12_2 : x (12 : ℤ) 2 = false := by
    cases hv : x (12 : ℤ) 2
    · rfl
    · have h := hp2 (12 : ℤ) hv
      rw [hc12] at h
      contradiction
  have hc_1_m4 := hcover 1 (by decide) (by decide) (-4 : ℤ)
  rcases hc_1_m4 with ⟨a_1_m4, ha_1_m4, ha1_1_m4, ha2_1_m4⟩
  have hc_1_m4 : (((x (-5 : ℤ) 2)) || ((x (-6 : ℤ) 2) && (x (-6 : ℤ) 3)) || ((x (-7 : ℤ) 3) && (x (-7 : ℤ) 4)) || ((x (-8 : ℤ) 4) && (x (-8 : ℤ) 5)) || ((x (-9 : ℤ) 5))) = true := by
    interval_cases a_1_m4 <;> norm_num at ha1_1_m4 ha2_1_m4 ⊢ <;> (try simp [hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at ha1_1_m4 ha2_1_m4 ⊢) <;> (try clear * - ha1_1_m4 ha2_1_m4) <;> tauto
  have hc_1_14 := hcover 1 (by decide) (by decide) (14 : ℤ)
  rcases hc_1_14 with ⟨a_1_14, ha_1_14, ha1_1_14, ha2_1_14⟩
  have hc_1_14 : (((x (13 : ℤ) 2)) || ((x (12 : ℤ) 2) && (x (12 : ℤ) 3)) || ((x (11 : ℤ) 3) && (x (11 : ℤ) 4)) || ((x (10 : ℤ) 4) && (x (10 : ℤ) 5)) || ((x (9 : ℤ) 5))) = true := by
    interval_cases a_1_14 <;> norm_num at ha1_1_14 ha2_1_14 ⊢ <;> (try simp [hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at ha1_1_14 ha2_1_14 ⊢) <;> (try clear * - ha1_1_14 ha2_1_14) <;> tauto
  have hc_3_m4 := hcover 3 (by decide) (by decide) (-4 : ℤ)
  rcases hc_3_m4 with ⟨a_3_m4, ha_3_m4, ha1_3_m4, ha2_3_m4⟩
  have hc_3_m4 : (((x (-4 : ℤ) 3)) || ((x (-5 : ℤ) 4)) || ((x (-6 : ℤ) 2) && (x (-6 : ℤ) 5)) || ((x (-7 : ℤ) 3)) || ((x (-8 : ℤ) 4))) = true := by
    interval_cases a_3_m4 <;> norm_num at ha1_3_m4 ha2_3_m4 ⊢ <;> (try simp [hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at ha1_3_m4 ha2_3_m4 ⊢) <;> (try clear * - ha1_3_m4 ha2_3_m4) <;> tauto
  have hc_3_1 := hcover 3 (by decide) (by decide) (1 : ℤ)
  rcases hc_3_1 with ⟨a_3_1, ha_3_1, ha1_3_1, ha2_3_1⟩
  have hc_3_1 : (((x (1 : ℤ) 3)) || ((x (-1 : ℤ) 2) && (x (-1 : ℤ) 5)) || ((x (-3 : ℤ) 4))) = true := by
    interval_cases a_3_1 <;> norm_num at ha1_3_1 ha2_3_1 ⊢ <;> (try simp [hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at ha1_3_1 ha2_3_1 ⊢) <;> (try clear * - ha1_3_1 ha2_3_1) <;> tauto
  have hc_3_4 := hcover 3 (by decide) (by decide) (4 : ℤ)
  rcases hc_3_4 with ⟨a_3_4, ha_3_4, ha1_3_4, ha2_3_4⟩
  have hc_3_4 : (((x (4 : ℤ) 3)) || ((x (3 : ℤ) 4)) || ((x (2 : ℤ) 2) && (x (2 : ℤ) 5)) || ((x (1 : ℤ) 3)) || ((x (0 : ℤ) 4))) = true := by
    interval_cases a_3_4 <;> norm_num at ha1_3_4 ha2_3_4 ⊢ <;> (try simp [hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at ha1_3_4 ha2_3_4 ⊢) <;> (try clear * - ha1_3_4 ha2_3_4) <;> tauto
  have hc_3_7 := hcover 3 (by decide) (by decide) (7 : ℤ)
  rcases hc_3_7 with ⟨a_3_7, ha_3_7, ha1_3_7, ha2_3_7⟩
  have hc_3_7 : (((x (7 : ℤ) 3)) || ((x (5 : ℤ) 2) && (x (5 : ℤ) 5)) || ((x (3 : ℤ) 4))) = true := by
    interval_cases a_3_7 <;> norm_num at ha1_3_7 ha2_3_7 ⊢ <;> (try simp [hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at ha1_3_7 ha2_3_7 ⊢) <;> (try clear * - ha1_3_7 ha2_3_7) <;> tauto
  have hc_3_8 := hcover 3 (by decide) (by decide) (8 : ℤ)
  rcases hc_3_8 with ⟨a_3_8, ha_3_8, ha1_3_8, ha2_3_8⟩
  have hc_3_8 : (((x (8 : ℤ) 3)) || ((x (7 : ℤ) 4)) || ((x (6 : ℤ) 2) && (x (6 : ℤ) 5)) || ((x (5 : ℤ) 3)) || ((x (4 : ℤ) 4))) = true := by
    interval_cases a_3_8 <;> norm_num at ha1_3_8 ha2_3_8 ⊢ <;> (try simp [hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at ha1_3_8 ha2_3_8 ⊢) <;> (try clear * - ha1_3_8 ha2_3_8) <;> tauto
  have hc_3_12 := hcover 3 (by decide) (by decide) (12 : ℤ)
  rcases hc_3_12 with ⟨a_3_12, ha_3_12, ha1_3_12, ha2_3_12⟩
  have hc_3_12 : (((x (12 : ℤ) 3)) || ((x (11 : ℤ) 4)) || ((x (10 : ℤ) 2) && (x (10 : ℤ) 5)) || ((x (9 : ℤ) 3)) || ((x (8 : ℤ) 4))) = true := by
    interval_cases a_3_12 <;> norm_num at ha1_3_12 ha2_3_12 ⊢ <;> (try simp [hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at ha1_3_12 ha2_3_12 ⊢) <;> (try clear * - ha1_3_12 ha2_3_12) <;> tauto
  have hc_5_m1 := hcover 5 (by decide) (by decide) (-1 : ℤ)
  rcases hc_5_m1 with ⟨a_5_m1, ha_5_m1, ha1_5_m1, ha2_5_m1⟩
  have hc_5_m1 : (((x (-1 : ℤ) 5)) || ((x (-3 : ℤ) 2))) = true := by
    interval_cases a_5_m1 <;> norm_num at ha1_5_m1 ha2_5_m1 ⊢ <;> (try simp [hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at ha1_5_m1 ha2_5_m1 ⊢) <;> (try clear * - ha1_5_m1 ha2_5_m1) <;> tauto
  have hc_5_3 := hcover 5 (by decide) (by decide) (3 : ℤ)
  rcases hc_5_3 with ⟨a_5_3, ha_5_3, ha1_5_3, ha2_5_3⟩
  have hc_5_3 : (((x (3 : ℤ) 5)) || ((x (1 : ℤ) 2))) = true := by
    interval_cases a_5_3 <;> norm_num at ha1_5_3 ha2_5_3 ⊢ <;> (try simp [hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at ha1_5_3 ha2_5_3 ⊢) <;> (try clear * - ha1_5_3 ha2_5_3) <;> tauto
  have hc_5_7 := hcover 5 (by decide) (by decide) (7 : ℤ)
  rcases hc_5_7 with ⟨a_5_7, ha_5_7, ha1_5_7, ha2_5_7⟩
  have hc_5_7 : (((x (7 : ℤ) 5)) || ((x (5 : ℤ) 2))) = true := by
    interval_cases a_5_7 <;> norm_num at ha1_5_7 ha2_5_7 ⊢ <;> (try simp [hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at ha1_5_7 ha2_5_7 ⊢) <;> (try clear * - ha1_5_7 ha2_5_7) <;> tauto
  have hc_5_11 := hcover 5 (by decide) (by decide) (11 : ℤ)
  rcases hc_5_11 with ⟨a_5_11, ha_5_11, ha1_5_11, ha2_5_11⟩
  have hc_5_11 : (((x (11 : ℤ) 5)) || ((x (9 : ℤ) 2))) = true := by
    interval_cases a_5_11 <;> norm_num at ha1_5_11 ha2_5_11 ⊢ <;> (try simp [hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at ha1_5_11 ha2_5_11 ⊢) <;> (try clear * - ha1_5_11 ha2_5_11) <;> tauto
  have he_m8 : rt1_one3 (x (-8 : ℤ) 4) (x (-9 : ℤ) 5) (x (-11 : ℤ) 3) = true := by
    have h := hexact (-8 : ℤ)
    norm_num [Finset.sum_range_succ, hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at h
    clear * - h
    cases h0 : x (-8 : ℤ) 4 <;> cases h1 : x (-9 : ℤ) 5 <;> cases h2 : x (-11 : ℤ) 3 <;> simp_all [rt1_one3]
  have he_m4 : rt1_one3 (x (-4 : ℤ) 4) (x (-5 : ℤ) 5) (x (-7 : ℤ) 3) = true := by
    have h := hexact (-4 : ℤ)
    norm_num [Finset.sum_range_succ, hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at h
    clear * - h
    cases h0 : x (-4 : ℤ) 4 <;> cases h1 : x (-5 : ℤ) 5 <;> cases h2 : x (-7 : ℤ) 3 <;> simp_all [rt1_one3]
  have he_m3 : rt1_one3 (x (-3 : ℤ) 4) (x (-5 : ℤ) 2) (x (-6 : ℤ) 3) = true := by
    have h := hexact (-3 : ℤ)
    norm_num [Finset.sum_range_succ, hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at h
    clear * - h
    cases h0 : x (-3 : ℤ) 4 <;> cases h1 : x (-5 : ℤ) 2 <;> cases h2 : x (-6 : ℤ) 3 <;> simp_all [rt1_one3]
  have he_0 : rt1_one3 (x (0 : ℤ) 4) (x (-1 : ℤ) 5) (x (-3 : ℤ) 3) = true := by
    have h := hexact (0 : ℤ)
    norm_num [Finset.sum_range_succ, hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at h
    clear * - h
    cases h0 : x (0 : ℤ) 4 <;> cases h1 : x (-1 : ℤ) 5 <;> cases h2 : x (-3 : ℤ) 3 <;> simp_all [rt1_one3]
  have he_3 : rt1_one3 (x (3 : ℤ) 4) (x (1 : ℤ) 2) (x (0 : ℤ) 3) = true := by
    have h := hexact (3 : ℤ)
    norm_num [Finset.sum_range_succ, hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at h
    clear * - h
    cases h0 : x (3 : ℤ) 4 <;> cases h1 : x (1 : ℤ) 2 <;> cases h2 : x (0 : ℤ) 3 <;> simp_all [rt1_one3]
  have he_4 : rt1_one3 (x (4 : ℤ) 4) (x (3 : ℤ) 5) (x (1 : ℤ) 3) = true := by
    have h := hexact (4 : ℤ)
    norm_num [Finset.sum_range_succ, hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at h
    clear * - h
    cases h0 : x (4 : ℤ) 4 <;> cases h1 : x (3 : ℤ) 5 <;> cases h2 : x (1 : ℤ) 3 <;> simp_all [rt1_one3]
  have he_7 : rt1_one3 (x (7 : ℤ) 4) (x (5 : ℤ) 2) (x (4 : ℤ) 3) = true := by
    have h := hexact (7 : ℤ)
    norm_num [Finset.sum_range_succ, hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at h
    clear * - h
    cases h0 : x (7 : ℤ) 4 <;> cases h1 : x (5 : ℤ) 2 <;> cases h2 : x (4 : ℤ) 3 <;> simp_all [rt1_one3]
  have he_8 : rt1_one3 (x (8 : ℤ) 4) (x (7 : ℤ) 5) (x (5 : ℤ) 3) = true := by
    have h := hexact (8 : ℤ)
    norm_num [Finset.sum_range_succ, hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at h
    clear * - h
    cases h0 : x (8 : ℤ) 4 <;> cases h1 : x (7 : ℤ) 5 <;> cases h2 : x (5 : ℤ) 3 <;> simp_all [rt1_one3]
  have he_10 : rt1_one3 (x (10 : ℤ) 4) (x (9 : ℤ) 5) (x (7 : ℤ) 3) = true := by
    have h := hexact (10 : ℤ)
    norm_num [Finset.sum_range_succ, hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at h
    clear * - h
    cases h0 : x (10 : ℤ) 4 <;> cases h1 : x (9 : ℤ) 5 <;> cases h2 : x (7 : ℤ) 3 <;> simp_all [rt1_one3]
  have he_11 : rt1_one3 (x (11 : ℤ) 4) (x (9 : ℤ) 2) (x (8 : ℤ) 3) = true := by
    have h := hexact (11 : ℤ)
    norm_num [Finset.sum_range_succ, hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at h
    clear * - h
    cases h0 : x (11 : ℤ) 4 <;> cases h1 : x (9 : ℤ) 2 <;> cases h2 : x (8 : ℤ) 3 <;> simp_all [rt1_one3]
  have he_12 : rt1_one3 (x (12 : ℤ) 4) (x (11 : ℤ) 5) (x (9 : ℤ) 3) = true := by
    have h := hexact (12 : ℤ)
    norm_num [Finset.sum_range_succ, hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at h
    clear * - h
    cases h0 : x (12 : ℤ) 4 <;> cases h1 : x (11 : ℤ) 5 <;> cases h2 : x (9 : ℤ) 3 <;> simp_all [rt1_one3]
  have he_15 : rt1_one3 (x (15 : ℤ) 4) (x (13 : ℤ) 2) (x (12 : ℤ) 3) = true := by
    have h := hexact (15 : ℤ)
    norm_num [Finset.sum_range_succ, hends0, hends7, hbm12, hbm11, hbm10, hbm9, hbm8, hbm7, hbm6, hbm5, hbm4, hbm3, hbm2, hbm1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hcm12, hcm11, hcm10, hcm9, hcm8, hcm7, hcm6, hcm5, hcm4, hcm3, hcm2, hcm1, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16] at h
    clear * - h
    cases h0 : x (15 : ℤ) 4 <;> cases h1 : x (13 : ℤ) 2 <;> cases h2 : x (12 : ℤ) 3 <;> simp_all [rt1_one3]
  have hn_m1 : rt1_one4 (x (-3 : ℤ) 2) (x (-4 : ℤ) 3) (x (-5 : ℤ) 4) (x (-6 : ℤ) 5) = true := by
    have h := hcount (-1 : ℤ) (by norm_num)
    norm_num at h
    clear * - h
    cases h0 : x (-3 : ℤ) 2 <;> cases h1 : x (-4 : ℤ) 3 <;> cases h2 : x (-5 : ℤ) 4 <;> cases h3 : x (-6 : ℤ) 5 <;> simp_all [rt1_one4]
  have hn_0 : rt1_one4 (x (-2 : ℤ) 2) (x (-3 : ℤ) 3) (x (-4 : ℤ) 4) (x (-5 : ℤ) 5) = true := by
    have h := hcount (0 : ℤ) (by norm_num)
    norm_num at h
    clear * - h
    cases h0 : x (-2 : ℤ) 2 <;> cases h1 : x (-3 : ℤ) 3 <;> cases h2 : x (-4 : ℤ) 4 <;> cases h3 : x (-5 : ℤ) 5 <;> simp_all [rt1_one4]
  exact rt1_count_defect_boolean_core x hp_m8_5 hp_m2_2 hp_2_2 hp_6_5 hp_10_5 hp_12_2 hc_1_m4 hc_1_14 hc_3_m4 hc_3_1 hc_3_4 hc_3_7 hc_3_8 hc_3_12 hc_5_m1 hc_5_3 hc_5_7 hc_5_11 he_m8 he_m4 he_m3 he_0 he_3 he_4 he_7 he_8 he_10 he_11 he_12 he_15 hn_m1 hn_0 hdefect
