import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate
import AFTD.Kb.Tcs.Op874FactorReachabilityGroup0
import AFTD.Kb.Tcs.Op874FactorReachabilityGroup1
import AFTD.Kb.Tcs.Op874FactorReachabilityGroup2
import AFTD.Kb.Tcs.Op874FactorReachabilityGroup3
import AFTD.Kb.Tcs.Op874FactorReachabilityGroup4
import AFTD.Kb.Tcs.Op874FactorReachabilityGroup5
import AFTD.Kb.Tcs.Op874FactorReachabilityGroup6
import AFTD.Kb.Tcs.Op874FactorReachabilityGroup7
import AFTD.Kb.Tcs.Op874FactorReachabilityGroup8
import AFTD.Kb.Tcs.Op874FactorReachabilityGroup9
import AFTD.Kb.Tcs.Op874FactorReachabilityGroup10
import AFTD.Kb.Tcs.Op874FactorReachabilityGroup11
import AFTD.Kb.Tcs.Op874FactorReachabilityGroup12
import AFTD.Kb.Tcs.Op874FactorTransitionRows0
import AFTD.Kb.Tcs.Op874FactorTransitionRows1
import AFTD.Kb.Tcs.Op874FactorTransitionRows2
import AFTD.Kb.Tcs.Op874FactorTransitionRows3
import AFTD.Kb.Tcs.Op874FactorTransitionRows4
import AFTD.Kb.Tcs.Op874FactorTransitionRows5
import AFTD.Kb.Tcs.Op874FactorTransitionRows6
import AFTD.Kb.Tcs.Op874FactorTransitionRows7
import AFTD.Kb.Tcs.Op874FactorTransitionRows8
import AFTD.Kb.Tcs.Op874FactorTransitionRows9
import AFTD.Kb.Tcs.Op874FactorTransitionRows10
import AFTD.Kb.Tcs.Op874FactorTransitionRows11
import AFTD.Kb.Tcs.Op874FactorTransitionRows12
import AFTD.Kb.Tcs.Op874FactorTransitionRows13
import AFTD.Kb.Tcs.Op874FactorTransitionRows14
import AFTD.Kb.Tcs.Op874FactorTransitionRows15
import AFTD.Kb.Tcs.Op874FactorTransitionRows16
import AFTD.Kb.Tcs.Op874FactorTransitionRows17
import AFTD.Kb.Tcs.Op874FactorTransitionRows18
import AFTD.Kb.Tcs.Op874FactorTransitionRows19
import AFTD.Kb.Tcs.Op874FactorTransitionRows20
import AFTD.Kb.Tcs.Op874FactorTransitionRows21
import AFTD.Kb.Tcs.Op874FactorTransitionRows22
import AFTD.Kb.Tcs.Op874FactorTransitionRows23
import AFTD.Kb.Tcs.Op874FactorPath

/-!
# op874_off_palette_even_word_factor_path

Topic: graphs   Node: 23ba52aec4b7

Provenance: helper lemma. Kernel-checked factor-word automaton for OP-874; experiment 35121, and explicit finite transition and closure certificates.

For an even list of at least two demands in four colors with a demand outside the distinguished pair {0,1}, there is a proper demand-covering factor-edge path with the required distinct boundary colors and with the remaining defect color used on an interior edge. The list of intermediate demands is supplied in reverse order.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem initial_0 : certMember 7442211984671671431960723459 certTree = true := by decide
theorem initial_1 : certMember 14973208296165987978867388468 certTree = true := by decide
theorem initial_2 : certMember 22415305167934371153826383413 certTree = true := by decide
theorem initial_3 : certMember 5220241521890145797 certTree = true := by decide

end In1051Cert

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
def allGroupKeys : List Nat := group0 ++ group1 ++ group2 ++ group3 ++ group4 ++ group5 ++ group6 ++ group7 ++ group8 ++ group9 ++ group10 ++ group11 ++ group12
theorem all_group_keys_checked : allGroupKeys.all checkCode = true := by
  simp only [allGroupKeys, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨op874_factor_reachability_group_0, op874_factor_reachability_group_1⟩, op874_factor_reachability_group_2⟩, op874_factor_reachability_group_3⟩, op874_factor_reachability_group_4⟩, op874_factor_reachability_group_5⟩, op874_factor_reachability_group_6⟩, op874_factor_reachability_group_7⟩, op874_factor_reachability_group_8⟩, op874_factor_reachability_group_9⟩, op874_factor_reachability_group_10⟩, op874_factor_reachability_group_11⟩, op874_factor_reachability_group_12⟩
end In1051Cert

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert

def treeKeys : CertTree → List Nat
  | .leaf => []
  | .node k l r => treeKeys l ++ k :: treeKeys r

theorem tree_keys_match : treeKeys certTree = allGroupKeys := by rfl
end In1051Cert

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem certMember_sound (key : Nat) (tree : CertTree) :
    certMember key tree = true → key ∈ treeKeys tree := by
  induction tree with
  | leaf => simp [certMember, treeKeys]
  | node k l r ihl ihr =>
    intro h
    simp only [certMember] at h
    by_cases he : key = k
    · simp [treeKeys, he]
    · simp only [he, if_false] at h
      by_cases hl : key < k
      · rw [if_pos hl] at h
        exact List.mem_append.mpr (Or.inl (ihl h))
      · rw [if_neg hl] at h
        exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (ihr h)))

theorem all_reachable_closed (key d : Nat)
    (hk : certMember key certTree = true) (hd : d < 4) :
    certMember (stepCode key d) certTree = true := by
  have hmem : key ∈ allGroupKeys := by
    rw [← tree_keys_match]
    exact certMember_sound key certTree hk
  have hg := (List.all_eq_true.mp all_group_keys_checked) key hmem
  simp only [checkCode, Bool.and_eq_true, List.all_eq_true] at hg
  have hdm : d ∈ ([0,1,2,3] : List Nat) := by interval_cases d <;> simp_all
  exact hg.2 d hdm

end In1051Cert

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert

theorem member_has_check (key : Nat) (h : certMember key certTree = true) :
    checkCode key = true := by
  have hmem : key ∈ allGroupKeys := by
    rw [← tree_keys_match]
    exact certMember_sound key certTree h
  exact (List.all_eq_true.mp all_group_keys_checked) key hmem

theorem member_good (key : Nat) (h : certMember key certTree = true)
    (hparity : (key % 6) / 3 = 0) (hpattern : key % 3 = 2) :
    (key % 12) / 6 = 1 := by
  have hc := member_has_check key h
  simp only [checkCode, Bool.and_eq_true] at hc
  have hgood := hc.1
  simp [hparity, hpattern] at hgood
  exact hgood
end In1051Cert

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert

theorem fold_bits (xs : List Nat) (f : Nat → Nat) (z j : Nat) :
    (xs.foldl (fun a i => a ||| f i) z).testBit j =
      (z.testBit j || xs.any (fun i => (f i).testBit j)) := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.any_cons, Nat.testBit_lor]
    simp only [Bool.or_assoc]

theorem advance_bits (mask d j : Nat) :
    (advance mask d).testBit j =
      (List.range 96).any (fun i => mask.testBit i && ((trans[d]!)[i]!).testBit j) := by
  unfold advance
  have hfun : (fun out i => if mask.testBit i then out ||| ((trans[d]!)[i]!) else out) =
      (fun out i => out ||| (if mask.testBit i then ((trans[d]!)[i]!) else 0)) := by
    funext out i
    cases h : mask.testBit i <;> simp [h]
  rw [hfun, fold_bits]
  simp only [Nat.zero_testBit, Bool.false_or]
  congr 1
  funext i
  cases h : mask.testBit i <;> simp [h]

theorem advance_iff (mask d j : Nat) :
    (advance mask d).testBit j = true ↔
      ∃ i < 96, mask.testBit i = true ∧ ((trans[d]!)[i]!).testBit j = true := by
  rw [advance_bits]
  simp

end In1051Cert

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert

theorem land_nonzero_iff (a b : Nat) :
    (a &&& b) ≠ 0 ↔ ∃ i, a.testBit i = true ∧ b.testBit i = true := by
  constructor
  · intro h
    by_contra hn
    apply h
    apply Nat.zero_of_testBit_eq_false
    intro i
    rw [Nat.testBit_land]
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  · rintro ⟨i, ha, hb⟩ heq
    have he := congrArg (fun n : Nat => n.testBit i) heq
    simp [Nat.testBit_land, ha, hb] at he

theorem close_bounded (d : Fin 4) : closing[d.val]! < 2 ^ 96 := by
  fin_cases d <;> decide

theorem close_iff (mask : Nat) (d : Fin 4) :
    (mask &&& closing[d.val]!) ≠ 0 ↔
      ∃ i < 96, mask.testBit i = true ∧ (closing[d.val]!).testBit i = true := by
  rw [land_nonzero_iff]
  constructor
  · rintro ⟨i, hi, hc⟩
    have hlt : i < 96 := by
      by_contra hn
      have hz := Nat.testBit_eq_false_of_lt (n := closing[d.val]!) (i := i)
        (lt_of_lt_of_le (close_bounded d) (Nat.pow_le_pow_right (by decide) (by omega)))
      simp_all
    exact ⟨i, hlt, hi, hc⟩
  · rintro ⟨i, _, hi, hc⟩
    exact ⟨i, hi, hc⟩
end In1051Cert

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem all_transition_rows (d : Fin 4) (i j : Fin 96) :
    ((trans[d.val]!)[i.val]!).testBit j.val =
      decide (wordStep d.val wordStates[i.val]! wordStates[j.val]!) := by
  fin_cases i
  · exact row_0 d j
  · exact row_1 d j
  · exact row_2 d j
  · exact row_3 d j
  · exact row_4 d j
  · exact row_5 d j
  · exact row_6 d j
  · exact row_7 d j
  · exact row_8 d j
  · exact row_9 d j
  · exact row_10 d j
  · exact row_11 d j
  · exact row_12 d j
  · exact row_13 d j
  · exact row_14 d j
  · exact row_15 d j
  · exact row_16 d j
  · exact row_17 d j
  · exact row_18 d j
  · exact row_19 d j
  · exact row_20 d j
  · exact row_21 d j
  · exact row_22 d j
  · exact row_23 d j
  · exact row_24 d j
  · exact row_25 d j
  · exact row_26 d j
  · exact row_27 d j
  · exact row_28 d j
  · exact row_29 d j
  · exact row_30 d j
  · exact row_31 d j
  · exact row_32 d j
  · exact row_33 d j
  · exact row_34 d j
  · exact row_35 d j
  · exact row_36 d j
  · exact row_37 d j
  · exact row_38 d j
  · exact row_39 d j
  · exact row_40 d j
  · exact row_41 d j
  · exact row_42 d j
  · exact row_43 d j
  · exact row_44 d j
  · exact row_45 d j
  · exact row_46 d j
  · exact row_47 d j
  · exact row_48 d j
  · exact row_49 d j
  · exact row_50 d j
  · exact row_51 d j
  · exact row_52 d j
  · exact row_53 d j
  · exact row_54 d j
  · exact row_55 d j
  · exact row_56 d j
  · exact row_57 d j
  · exact row_58 d j
  · exact row_59 d j
  · exact row_60 d j
  · exact row_61 d j
  · exact row_62 d j
  · exact row_63 d j
  · exact row_64 d j
  · exact row_65 d j
  · exact row_66 d j
  · exact row_67 d j
  · exact row_68 d j
  · exact row_69 d j
  · exact row_70 d j
  · exact row_71 d j
  · exact row_72 d j
  · exact row_73 d j
  · exact row_74 d j
  · exact row_75 d j
  · exact row_76 d j
  · exact row_77 d j
  · exact row_78 d j
  · exact row_79 d j
  · exact row_80 d j
  · exact row_81 d j
  · exact row_82 d j
  · exact row_83 d j
  · exact row_84 d j
  · exact row_85 d j
  · exact row_86 d j
  · exact row_87 d j
  · exact row_88 d j
  · exact row_89 d j
  · exact row_90 d j
  · exact row_91 d j
  · exact row_92 d j
  · exact row_93 d j
  · exact row_94 d j
  · exact row_95 d j
end In1051Cert

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert

def runMaskRev (mask : Nat) : List (Fin 4) → Nat
  | [] => mask
  | d :: ds => advance (runMaskRev mask ds) d.val

def wordTrace (first : Fin 4) : List (Fin 4) → Fin 96 → Prop
  | [], j => initialWordState first.val wordStates[j.val]!
  | d :: ds, j => ∃ i : Fin 96, wordTrace first ds i ∧
      wordStep d.val wordStates[i.val]! wordStates[j.val]!

theorem trace_mask_iff
    (hrows : ∀ (d : Fin 4) (i j : Fin 96),
      ((trans[d.val]!)[i.val]!).testBit j.val =
        decide (wordStep d.val wordStates[i.val]! wordStates[j.val]!))
    (first : Fin 4) (ds : List (Fin 4)) (j : Fin 96) :
    (runMaskRev (initialMask first) ds).testBit j.val = true ↔ wordTrace first ds j := by
  induction ds generalizing j with
  | nil =>
    simp only [runMaskRev, wordTrace, initial_mask_correct, decide_eq_true_eq]
  | cons d ds ih =>
    rw [runMaskRev, advance_iff]
    simp only [wordTrace]
    constructor
    · rintro ⟨i, hi, hmask, htrans⟩
      let idx : Fin 96 := ⟨i, hi⟩
      refine ⟨idx, (ih idx).1 hmask, ?_⟩
      have he := hrows d idx j
      have hdec : decide (wordStep d.val wordStates[idx.val]! wordStates[j.val]!) = true := by
        rw [← he]
        exact htrans
      exact of_decide_eq_true hdec
    · rintro ⟨i, htrace, hstep⟩
      refine ⟨i.val, i.isLt, (ih i).2 htrace, ?_⟩
      rw [hrows]
      exact decide_eq_true hstep

theorem trace_accept_iff
    (hrows : ∀ (d : Fin 4) (i j : Fin 96),
      ((trans[d.val]!)[i.val]!).testBit j.val =
        decide (wordStep d.val wordStates[i.val]! wordStates[j.val]!))
    (first last : Fin 4) (ds : List (Fin 4)) :
    (runMaskRev (initialMask first) ds &&& closing[last.val]!) ≠ 0 ↔
      ∃ i : Fin 96, wordTrace first ds i ∧ closingWordState last.val wordStates[i.val]! := by
  rw [close_iff]
  constructor
  · rintro ⟨i, hi, hmask, hclose⟩
    let idx : Fin 96 := ⟨i, hi⟩
    refine ⟨idx, (trace_mask_iff hrows first ds idx).1 hmask, ?_⟩
    have he := closing_mask_correct last idx
    have hdec : decide (closingWordState last.val wordStates[idx.val]!) = true := by
      rw [← he]
      exact hclose
    exact of_decide_eq_true hdec
  · rintro ⟨i, htrace, hclose⟩
    refine ⟨i.val, i.isLt, (trace_mask_iff hrows first ds i).2 htrace, ?_⟩
    rw [closing_mask_correct]
    exact decide_eq_true hclose
end In1051Cert

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert

def initialCode (d : Fin 4) : Nat :=
  initialMask d * 12 + 3 + (if d.val < 2 then d.val else 2)

theorem initial_mask_field (d : Fin 4) : initialCode d / 12 = initialMask d := by
  fin_cases d <;> decide

theorem initial_parity_field (d : Fin 4) : (initialCode d % 6) / 3 = 1 := by
  fin_cases d <;> decide

theorem initial_pattern_field (d : Fin 4) : initialCode d % 3 = (if d.val < 2 then d.val else 2) := by
  fin_cases d <;> decide

theorem step_mask_field (key d : Nat) :
    stepCode key d / 12 = advance (key / 12) d := by
  unfold stepCode
  dsimp only
  split_ifs <;> omega

theorem packed_accept (m a p q : Nat) (ha : a = 0 ∨ a = 6)
    (hp : p ≤ 1) (hq : q ≤ 2) :
    ((m * 12 + a + p * 3 + q) % 12) / 6 = a / 6 := by
  have heq : m * 12 + a + p * 3 + q = 12 * m + (a + p * 3 + q) := by omega
  rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rcases ha with rfl | rfl <;> omega

theorem step_accept_field (key d : Nat) :
    (stepCode key d % 12) / 6 = (if (key / 12) &&& closing[d]! ≠ 0 then 1 else 0) := by
  have hp : (1 - (key % 6) / 3) ≤ 1 := by omega
  have hq : (if key % 3 < 2 ∧ d = 1 - key % 3 then d else 2) ≤ 2 := by
    split_ifs <;> omega
  have ha : (if (key / 12) &&& closing[d]! != 0 then 6 else 0) = 0 ∨
      (if (key / 12) &&& closing[d]! != 0 then 6 else 0) = 6 := by
    split_ifs <;> simp
  have hf := packed_accept (advance (key / 12) d)
    (if (key / 12) &&& closing[d]! != 0 then 6 else 0)
    (1 - key % 6 / 3) (if key % 3 < 2 ∧ d = 1 - key % 3 then d else 2) ha hp hq
  simpa only [stepCode, ite_div, Nat.reduceDiv, bne_iff_ne] using hf

theorem step_parity_field (key d : Nat) :
    (stepCode key d % 6) / 3 = 1 - (key % 6) / 3 := by
  unfold stepCode
  dsimp only
  split_ifs <;> omega

theorem step_pattern_field (key d : Nat) :
    stepCode key d % 3 = (if key % 3 < 2 ∧ d = 1 - key % 3 then d else 2) := by
  unfold stepCode
  dsimp only
  split_ifs <;> omega
end In1051Cert

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert

def runCodeRev (first : Fin 4) : List (Fin 4) → Nat
  | [] => initialCode first
  | d :: ds => stepCode (runCodeRev first ds) d.val

theorem initial_cert (d : Fin 4) : certMember (initialCode d) certTree = true := by
  fin_cases d
  · simpa [initialCode, initialMask] using initial_0
  · simpa [initialCode, initialMask] using initial_1
  · simpa [initialCode, initialMask] using initial_2
  · simpa [initialCode, initialMask] using initial_3

theorem run_cert (first : Fin 4) (ds : List (Fin 4)) :
    certMember (runCodeRev first ds) certTree = true := by
  induction ds with
  | nil => exact initial_cert first
  | cons d ds ih => exact all_reachable_closed _ d.val ih d.isLt

theorem run_mask (first : Fin 4) (ds : List (Fin 4)) :
    runCodeRev first ds / 12 = runMaskRev (initialMask first) ds := by
  induction ds with
  | nil => exact initial_mask_field first
  | cons d ds ih => simp only [runCodeRev, runMaskRev, step_mask_field, ih]

theorem run_parity (first : Fin 4) (ds : List (Fin 4)) :
    (runCodeRev first ds % 6) / 3 = (ds.length + 1) % 2 := by
  induction ds with
  | nil => simpa [runCodeRev] using initial_parity_field first
  | cons d ds ih =>
    simp only [runCodeRev, step_parity_field, List.length_cons]
    rw [ih]
    omega

theorem run_off_pattern (first : Fin 4) (ds : List (Fin 4))
    (hoff : 2 ≤ first.val ∨ ∃ d ∈ ds, 2 ≤ d.val) :
    runCodeRev first ds % 3 = 2 := by
  induction ds with
  | nil =>
    simp only [List.not_mem_nil, false_and, exists_false, or_false] at hoff
    rw [runCodeRev, initial_pattern_field]
    split_ifs <;> omega
  | cons d ds ih =>
    simp only [List.mem_cons, exists_eq_or_imp] at hoff
    rcases hoff with hf | hd | htail
    · have hprev := ih (Or.inl hf)
      simp only [runCodeRev, step_pattern_field, hprev]
      simp
    · simp only [runCodeRev, step_pattern_field]
      split_ifs <;> omega
    · have hprev := ih (Or.inr htail)
      simp only [runCodeRev, step_pattern_field, hprev]
      simp

theorem off_palette_even_word_has_accepting_trace
    (first last : Fin 4) (ds : List (Fin 4))
    (heven : (ds.length + 2) % 2 = 0)
    (hoff : 2 ≤ first.val ∨ 2 ≤ last.val ∨ ∃ d ∈ ds, 2 ≤ d.val) :
    ∃ i : Fin 96, wordTrace first ds i ∧ closingWordState last.val wordStates[i.val]! := by
  have hc := run_cert first (last :: ds)
  have hp : (runCodeRev first (last :: ds) % 6) / 3 = 0 := by
    rw [run_parity]
    simp only [List.length_cons]
    omega
  have ht : runCodeRev first (last :: ds) % 3 = 2 := by
    apply run_off_pattern
    simp only [List.mem_cons, exists_eq_or_imp]
    exact hoff
  have hgood := member_good _ hc hp ht
  simp only [runCodeRev, step_accept_field, run_mask] at hgood
  have haccept : (runMaskRev (initialMask first) ds &&& closing[last.val]!) ≠ 0 := by
    split_ifs at hgood <;> simp_all
  exact (trace_accept_iff all_transition_rows first last ds).1 haccept
end In1051Cert

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert

theorem word_trace_to_factor_path (first : Fin 4) (ds : List (Fin 4)) (j : Fin 96)
    (htrace : wordTrace first ds j) :
    ∃ firstC : Nat, ∃ rest : List Nat,
      firstC ≠ wordStates[j.val]!.a ∧
      FactorPath wordStates[j.val]!.b (first :: ds.reverse)
        (firstC :: rest) wordStates[j.val]!.c ∧
      (wordStates[j.val]!.used = true ↔ wordStates[j.val]!.u ∈ firstC :: rest) := by
  induction ds generalizing j with
  | nil =>
    change initialWordState first.val wordStates[j.val]! at htrace
    rcases htrace with ⟨hca, hcb, hd, hu⟩
    refine ⟨wordStates[j.val]!.c, [], hca, ?_, ?_⟩
    · simpa using (FactorPath.extend (FactorPath.base (b := wordStates[j.val]!.b))
        first wordStates[j.val]!.c hcb (all_word_states_valid j).2.2.2.1 hd)
    · simp only [List.mem_singleton]
      rw [hu]
      simp only [beq_iff_eq]
      exact eq_comm
  | cons d ds ih =>
    change ∃ i : Fin 96, wordTrace first ds i ∧
      wordStep d.val wordStates[i.val]! wordStates[j.val]! at htrace
    rcases htrace with ⟨i, htrace, hstep⟩
    rcases hstep with ⟨ha, hb, hu, hc, hd, hused⟩
    obtain ⟨firstC, rest, hfirst, hpath, hmem⟩ := ih i htrace
    refine ⟨firstC, rest ++ [wordStates[j.val]!.c], ?_, ?_, ?_⟩
    · simpa [ha] using hfirst
    · have hnew := FactorPath.extend hpath d wordStates[j.val]!.c hc (all_word_states_valid j).2.2.2.1 hd
      simpa [List.reverse_cons, List.cons_append, hb] using hnew
    · rw [hused, Bool.or_eq_true]
      rw [hmem, hu]
      change (wordStates[i.val]!.u ∈ firstC :: rest ∨
        (wordStates[j.val]!.c == wordStates[i.val]!.u) = true) ↔
        wordStates[i.val]!.u ∈ (firstC :: rest) ++ [wordStates[j.val]!.c]
      simp only [List.mem_append, List.mem_singleton, beq_iff_eq]
      exact or_congr Iff.rfl eq_comm
end In1051Cert
open In1051Cert

theorem op874_off_palette_even_word_factor_path
    (first last : Fin 4) (ds : List (Fin 4))
    (heven : (ds.length + 2) % 2 = 0)
    (hoff : 2 ≤ first.val ∨ 2 ≤ last.val ∨ ∃ d ∈ ds, 2 ≤ d.val) :
    ∃ x : WordState, ∃ firstC : Nat, ∃ rest : List Nat,
      validWordState x ∧ firstC ≠ x.a ∧
      FactorPath x.b (first :: ds.reverse) (firstC :: rest) x.c ∧
      x.c ≠ x.a ∧ (last.val = x.c ∨ last.val = x.a) ∧
      x.u ∈ firstC :: rest := by
  obtain ⟨i, htrace, hclose⟩ := off_palette_even_word_has_accepting_trace first last ds heven hoff
  obtain ⟨firstC, rest, hfirst, hpath, hmem⟩ := word_trace_to_factor_path first ds i htrace
  rcases hclose with ⟨hu, hc, hd⟩
  exact ⟨wordStates[i.val]!, firstC, rest, all_word_states_valid i, hfirst, hpath, hc, hd, hmem.mp hu⟩
