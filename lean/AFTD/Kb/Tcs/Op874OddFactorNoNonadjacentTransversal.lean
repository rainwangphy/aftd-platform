import AFTD.Prelude
import AFTD.Kb.Tcs.Op874OddFactorTransversalSlots
import AFTD.Kb.Tcs.Op874OddFactorTransversalChecks0
import AFTD.Kb.Tcs.Op874OddFactorTransversalChecks1
import AFTD.Kb.Tcs.Op874OddFactorTransversalChecks2

/-!
# op874_odd_factor_no_nonadjacent_transversal

Topic: graphs   Node: 9c5d1c8878f4

Provenance: helper lemma. Explicit three odd-cycle independent-transversal obstruction based on https://arxiv.org/html/2309.12150 section 2.2; experiment 35359.

Every selection of one vertex from each of the seven displayed triples contains adjacent vertices in one of the three seven-cycles. Thus this one-sided nonadjacent defect-selection condition fails for the corresponding prescribed odd-cycle factor.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Obstruction
theorem every_choice_has_conflict (c : Fin 2187) : bad c.val = true := by
  by_cases h0 : c.val < 243
  · exact first_243 ⟨c.val, h0⟩
  by_cases h1 : c.val < 486
  · have hh : c.val - 243 < 243 := by omega
    have he : c.val - 243 + 243 = c.val := by omega
    simpa only [he] using block_1 ⟨c.val - 243, hh⟩
  by_cases h2 : c.val < 729
  · have hh : c.val - 486 < 243 := by omega
    have he : c.val - 486 + 486 = c.val := by omega
    simpa only [he] using block_2 ⟨c.val - 486, hh⟩
  by_cases h3 : c.val < 972
  · have hh : c.val - 729 < 243 := by omega
    have he : c.val - 729 + 729 = c.val := by omega
    simpa only [he] using block_3 ⟨c.val - 729, hh⟩
  by_cases h4 : c.val < 1215
  · have hh : c.val - 972 < 243 := by omega
    have he : c.val - 972 + 972 = c.val := by omega
    simpa only [he] using block_4 ⟨c.val - 972, hh⟩
  by_cases h5 : c.val < 1458
  · have hh : c.val - 1215 < 243 := by omega
    have he : c.val - 1215 + 1215 = c.val := by omega
    simpa only [he] using block_5 ⟨c.val - 1215, hh⟩
  by_cases h6 : c.val < 1701
  · have hh : c.val - 1458 < 243 := by omega
    have he : c.val - 1458 + 1458 = c.val := by omega
    simpa only [he] using block_6 ⟨c.val - 1458, hh⟩
  by_cases h7 : c.val < 1944
  · have hh : c.val - 1701 < 243 := by omega
    have he : c.val - 1701 + 1701 = c.val := by omega
    simpa only [he] using block_7 ⟨c.val - 1701, hh⟩
  have hh : c.val - 1944 < 243 := by omega
  have he : c.val - 1944 + 1944 = c.val := by omega
  simpa only [he] using block_8 ⟨c.val - 1944, hh⟩
end In1081Obstruction
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Obstruction

def encode (f : Fin 7 → Fin 3) : Nat :=
  (f 0).val + 3 * (f 1).val + 9 * (f 2).val + 27 * (f 3).val +
  81 * (f 4).val + 243 * (f 5).val + 729 * (f 6).val

theorem encode_lt (f : Fin 7 → Fin 3) : encode f < 2187 := by
  have h0 := (f 0).isLt
  have h1 := (f 1).isLt
  have h2 := (f 2).isLt
  have h3 := (f 3).isLt
  have h4 := (f 4).isLt
  have h5 := (f 5).isLt
  have h6 := (f 6).isLt
  dsimp [encode]
  omega

theorem encode_digit (f : Fin 7 → Fin 3) (i : Fin 7) :
    (encode f / 3 ^ i.val) % 3 = (f i).val := by
  have h0 := (f 0).isLt
  have h1 := (f 1).isLt
  have h2 := (f 2).isLt
  have h3 := (f 3).isLt
  have h4 := (f 4).isLt
  have h5 := (f 5).isLt
  have h6 := (f 6).isLt
  fin_cases i <;>
    first
    | change (encode f / 1) % 3 = (f 0).val
    | change (encode f / 3) % 3 = (f 1).val
    | change (encode f / 9) % 3 = (f 2).val
    | change (encode f / 27) % 3 = (f 3).val
    | change (encode f / 81) % 3 = (f 4).val
    | change (encode f / 243) % 3 = (f 5).val
    | change (encode f / 729) % 3 = (f 6).val
  all_goals simp only [encode, Nat.div_one] <;> omega
end In1081Obstruction
open In1081Obstruction

theorem op874_odd_factor_no_nonadjacent_transversal (f : Fin 7 → Fin 3) :
    ∃ i j : Fin 7, i < j ∧
      conflict ((slots[i.val]!)[(f i).val]!) ((slots[j.val]!)[(f j).val]!) = true := by
  have h := every_choice_has_conflict ⟨encode f, encode_lt f⟩
  simp only [bad, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨i, hi, j, hj, hij, hc⟩ := h
  let ii : Fin 7 := ⟨i, hi⟩
  let jj : Fin 7 := ⟨j, hj⟩
  refine ⟨ii, jj, hij, ?_⟩
  have hdi := encode_digit f ii
  have hdj := encode_digit f jj
  change (encode f / 3 ^ i) % 3 = (f ii).val at hdi
  change (encode f / 3 ^ j) % 3 = (f jj).val at hdj
  simpa only [pick, hdi, hdj] using hc
