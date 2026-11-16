import AFTD.Prelude

/-!
# op_1239_candidate36_recurrence_values

Topic: combinatorics   Node: 04dfbf1ea57e

Provenance: helper lemma. OP-1239: rooted-state arithmetic for the 36-vertex candidate, computed independently in experiments 28328 and 28332.

The ten coefficients produced by the explicit rooted recurrence for the 36-vertex candidate are 8339521563, 20789154045, 21845817576, 12541674376, 4251096840, 852919728, 94592768, 4666944, 32640, and 256.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PetrialCert

def padd : List Nat → List Nat → List Nat
  | [], b => b
  | a, [] => a
  | a::as, b::bs => (a+b)::padd as bs

def psub : List Nat → List Nat → List Nat
  | [], _ => []
  | a, [] => a
  | a::as, b::bs => (a-b)::psub as bs

def pmul : List Nat → List Nat → List Nat
  | [], _ => []
  | a::as, b => padd (b.map (a * ·)) (0 :: pmul as b)

def combine (xs : List (List Nat × List Nat)) : List Nat × List Nat :=
  let s := xs.foldl (fun p x => pmul p x.1) [1]
  let d := xs.foldl (fun p x => pmul p (padd x.1 (0::x.2))) [1]
  (padd s ((psub d s).drop 1 |>.map (2 * ·)), s)

def s71 := combine []
theorem s71_cert : s71 = ([1], [1]) := by
  simp only [s71]
  decide

def s34 := combine []
theorem s34_cert : s34 = ([1], [1]) := by
  simp only [s34]
  decide

def s73 := combine []
theorem s73_cert : s73 = ([1], [1]) := by
  simp only [s73]
  decide

def s42 := combine [s71]
theorem s42_cert : s42 = ([3], [1]) := by
  simp only [s42, s71_cert]
  decide

def s31 := combine [s34]
theorem s31_cert : s31 = ([3], [1]) := by
  simp only [s31, s34_cert]
  decide

def s52 := combine []
theorem s52_cert : s52 = ([1], [1]) := by
  simp only [s52]
  decide

def s25 := combine []
theorem s25_cert : s25 = ([1], [1]) := by
  simp only [s25]
  decide

def s61 := combine []
theorem s61_cert : s61 = ([1], [1]) := by
  simp only [s61]
  decide

def s46 := combine [s73]
theorem s46_cert : s46 = ([3], [1]) := by
  simp only [s46, s73_cert]
  decide

def s33 := combine []
theorem s33_cert : s33 = ([1], [1]) := by
  simp only [s33]
  decide

def s17 := combine []
theorem s17_cert : s17 = ([1], [1]) := by
  simp only [s17]
  decide

def s60 := combine []
theorem s60_cert : s60 = ([1], [1]) := by
  simp only [s60]
  decide

def s26 := combine [s31, s42]
theorem s26_cert : s26 = ([21, 2], [9]) := by
  simp only [s26, s31_cert, s42_cert]
  decide

def s30 := combine []
theorem s30_cert : s30 = ([1], [1]) := by
  simp only [s30]
  decide

def s15 := combine []
theorem s15_cert : s15 = ([1], [1]) := by
  simp only [s15]
  decide

def s10 := combine [s25, s52]
theorem s10_cert : s10 = ([5, 2], [1]) := by
  simp only [s10, s25_cert, s52_cert]
  decide

def s21 := combine [s46, s61]
theorem s21_cert : s21 = ([11, 2], [3]) := by
  simp only [s21, s46_cert, s61_cert]
  decide

def s9 := combine []
theorem s9_cert : s9 = ([1], [1]) := by
  simp only [s9]
  decide

def s68 := combine []
theorem s68_cert : s68 = ([1], [1]) := by
  simp only [s68]
  decide

def s41 := combine []
theorem s41_cert : s41 = ([1], [1]) := by
  simp only [s41]
  decide

def s14 := combine [s33]
theorem s14_cert : s14 = ([3], [1]) := by
  simp only [s14, s33_cert]
  decide

def s13 := combine [s17]
theorem s13_cert : s13 = ([3], [1]) := by
  simp only [s13, s17_cert]
  decide

def s16 := combine [s26, s60]
theorem s16_cert : s16 = ([81, 24], [21, 2]) := by
  simp only [s16, s26_cert, s60_cert]
  decide

def s12 := combine [s30]
theorem s12_cert : s12 = ([3], [1]) := by
  simp only [s12, s30_cert]
  decide

def s7 := combine [s10, s15]
theorem s7_cert : s7 = ([17, 8], [5, 2]) := by
  simp only [s7, s10_cert, s15_cert]
  decide

def s6 := combine [s9, s21]
theorem s6_cert : s6 = ([39, 12], [11, 2]) := by
  simp only [s6, s9_cert, s21_cert]
  decide

def s35 := combine []
theorem s35_cert : s35 = ([1], [1]) := by
  simp only [s35]
  decide

def s11 := combine [s41, s68]
theorem s11_cert : s11 = ([5, 2], [1]) := by
  simp only [s11, s41_cert, s68_cert]
  decide

def s50 := combine []
theorem s50_cert : s50 = ([1], [1]) := by
  simp only [s50]
  decide

def s5 := combine [s13, s14]
theorem s5_cert : s5 = ([21, 2], [9]) := by
  simp only [s5, s13_cert, s14_cert]
  decide

def s4 := combine [s12, s16]
theorem s4_cert : s4 = ([531, 174, 4], [243, 72]) := by
  simp only [s4, s12_cert, s16_cert]
  decide

def s2 := combine [s6, s7]
theorem s2_cert : s2 = ([1427, 1146, 240, 8], [663, 516, 96]) := by
  simp only [s2, s6_cert, s7_cert]
  decide

def s8 := combine [s11, s35]
theorem s8_cert : s8 = ([17, 8], [5, 2]) := by
  simp only [s8, s11_cert, s35_cert]
  decide

def s3 := combine [s5, s50]
theorem s3_cert : s3 = ([81, 24], [21, 2]) := by
  simp only [s3, s5_cert, s50_cert]
  decide

def s1 := combine [s2, s4]
theorem s1_cert : s1 = ([2155365, 2720202, 1247288, 247536, 18096, 32], [757737, 856824, 332552, 50592, 2352, 32]) := by
  simp only [s1, s2_cert, s4_cert]
  decide

def s0 := combine [s1, s3, s8]
theorem s0_cert : s0 = ([8339521563, 17821216440, 15824033982, 7537795408, 2070824856, 327124224, 27912416, 1158720, 26496, 256], [2967937605, 6021783594, 5003878968, 2180271984, 525795504, 66680352, 3508224, 6144]) := by
  simp only [s0, s1_cert, s3_cert, s8_cert]
  decide

end PetrialCert

/-- A checked arithmetic certificate for a recursively computed candidate coefficient list; relating the recurrence to matrix nullities remains a separate obligation. -/
theorem op_1239_candidate36_recurrence_values : (PetrialCert.padd PetrialCert.s0.1 (0 :: PetrialCert.s0.2)).take 10 = [8339521563, 20789154045, 21845817576, 12541674376, 4251096840, 852919728, 94592768, 4666944, 32640, 256] := by
  rw [PetrialCert.s0_cert]
  decide
