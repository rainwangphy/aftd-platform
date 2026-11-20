import AFTD.Prelude
import AFTD.Kb.Tcs.Op874SeparatedWindowAutomatonAcceptance
import AFTD.Kb.Tcs.Op874SeparatedWordAutomatonSafety

/-!
# op874_separated_defect_flags_are_admissible

Topic: graphs   Node: 44115b3b12d4

Provenance: helper lemma. Cyclic-index transfer for the OP-874 separated-defect automaton.

Starting at a selected defect in a cycle of length at least six, the cyclic indicator word for defects separated by at least three starts with a forced step and is accepted by the automaton cooldown and length conditions.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Flags
open In1081Separated

variable (n : ℕ) [NeZero n] (hn : 6 ≤ n) (Q : Finset (Fin n)) (q0 : Fin n)
  (hq0 : q0 ∈ Q) (hsep : ∀ q ∈ Q, q+1 ∉ Q ∧ q+2 ∉ Q)

def flags : List Bool := List.ofFn fun i : Fin (n-1) => decide (q0 + Fin.ofNat n (i.val+1) ∈ Q)

theorem flag_value (i : ℕ) (hi : i < n-1) :
    (flags n Q q0)[i]? = some (decide (q0 + Fin.ofNat n (i+1) ∈ Q)) := by
  rw [List.getElem?_eq_getElem (by simp [flags]; omega)]
  simp [flags]

theorem flag_sep (hn : 6 ≤ n) (hsep : ∀ q ∈ Q, q+1 ∉ Q ∧ q+2 ∉ Q) : separated (flags n Q q0) := by
  intro i hi
  have hi' := (List.getElem?_eq_some_iff.mp hi)
  have ilt : i < n-1 := by simpa [flags] using hi'.choose
  have hf := flag_value n Q q0 i ilt
  rw [hf] at hi
  have hq : q0 + Fin.ofNat n (i+1) ∈ Q := by simpa using hi
  have hs := hsep _ hq
  constructor
  · intro bad
    have jlt : i+1 < n-1 := by
      have := (List.getElem?_eq_some_iff.mp bad).choose
      simpa [flags] using this
    rw [flag_value n Q q0 (i+1) jlt] at bad
    have hb : q0 + Fin.ofNat n (i+1+1) ∈ Q := by simpa using bad
    apply hs.1
    have he : Fin.ofNat n (i+1+1) = Fin.ofNat n (i+1) + 1 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_ofNat]
      change (i+1+1)%n = ((i+1)%n + (1%n))%n
      rw [Nat.mod_eq_of_lt (by omega : i+1 < n), Nat.mod_eq_of_lt (by omega : 1 < n)]
    rw [he, ← add_assoc] at hb
    exact hb
  · intro bad
    have jlt : i+2 < n-1 := by
      have := (List.getElem?_eq_some_iff.mp bad).choose
      simpa [flags] using this
    rw [flag_value n Q q0 (i+2) jlt] at bad
    have hb : q0 + Fin.ofNat n (i+2+1) ∈ Q := by simpa using bad
    apply hs.2
    have he : Fin.ofNat n (i+2+1) = Fin.ofNat n (i+1) + 2 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_ofNat]
      change (i+2+1)%n = ((i+1)%n + (2%n))%n
      rw [Nat.mod_eq_of_lt (by omega : i+1 < n), Nat.mod_eq_of_lt (by omega : 2 < n)]
    rw [he, ← add_assoc] at hb
    exact hb

theorem flag_safe (hn : 6 ≤ n) (hq0 : q0 ∈ Q) (hsep : ∀ q ∈ Q, q+1 ∉ Q ∧ q+2 ∉ Q) : safePrefix 2 (flags n Q q0) := by
  intro i hi bad
  have ilt : i < n-1 := by omega
  rw [flag_value n Q q0 i ilt] at bad
  have hb : q0 + Fin.ofNat n (i+1) ∈ Q := by simpa using bad
  have hs := hsep q0 hq0
  interval_cases i
  · apply hs.1
    have he : Fin.ofNat n (0+1) = (1 : Fin n) := by
      apply Fin.ext
      simp [Fin.val_ofNat, Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < n)]
    rwa [he] at hb
  · apply hs.2
    have he : Fin.ofNat n (1+1) = (2 : Fin n) := by
      apply Fin.ext
      simp [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 2 < n)]
    rwa [he] at hb
theorem last_false (hn : 6 ≤ n) (hq0 : q0 ∈ Q)
    (hsep : ∀ q ∈ Q, q+1 ∉ Q ∧ q+2 ∉ Q) :
    (flags n Q q0)[n-3]? = some false ∧ (flags n Q q0)[n-2]? = some false := by
  have h1 : (q0 + Fin.ofNat n (n-2)) + 2 = q0 := by
    have he : Fin.ofNat n (n-2) + 2 = (0 : Fin n) := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_ofNat]
      change ((n-2)%n + 2%n)%n = 0
      rw [Nat.mod_eq_of_lt (by omega : n-2 < n), Nat.mod_eq_of_lt (by omega : 2 < n)]
      have : n-2+2=n := by omega
      rw [this, Nat.mod_self]
    rw [add_assoc, he, add_zero]
  have h2 : (q0 + Fin.ofNat n (n-1)) + 1 = q0 := by
    have he : Fin.ofNat n (n-1) + 1 = (0 : Fin n) := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_ofNat]
      change ((n-1)%n + 1%n)%n = 0
      rw [Nat.mod_eq_of_lt (by omega : n-1 < n), Nat.mod_eq_of_lt (by omega : 1 < n)]
      have : n-1+1=n := by omega
      rw [this, Nat.mod_self]
    rw [add_assoc, he, add_zero]
  have hn1 : q0 + Fin.ofNat n (n-2) ∉ Q := by
    intro h
    apply (hsep _ h).2
    rwa [h1]
  have hn2 : q0 + Fin.ofNat n (n-1) ∉ Q := by
    intro h
    apply (hsep _ h).1
    rwa [h2]
  constructor
  · rw [flag_value n Q q0 (n-3) (by omega)]
    have he : n-3+1 = n-2 := by omega
    simp only [he, Option.some.injEq, decide_eq_false_iff_not]
    exact hn1
  · rw [flag_value n Q q0 (n-2) (by omega)]
    have he : n-2+1 = n-1 := by omega
    simp only [he, Option.some.injEq, decide_eq_false_iff_not]
    exact hn2
theorem flag_end (hn : 6 ≤ n) (hq0 : q0 ∈ Q)
    (hsep : ∀ q ∈ Q, q+1 ∉ Q ∧ q+2 ∉ Q) :
    (flags n Q q0).drop (n-3) = [false, false] := by
  have hl := last_false n Q q0 hn hq0 hsep
  apply List.ext_getElem
  · simp [flags, List.length_drop]; omega
  · intro i hi hj
    rw [List.getElem_drop]
    have ii : i < 2 := by simpa using hj
    interval_cases i
    · have h := (List.getElem?_eq_some_iff.mp hl.1).choose_spec
      simpa using h
    · have h := (List.getElem?_eq_some_iff.mp hl.2).choose_spec
      have he : n-3+1=n-2 := by omega
      simpa [he] using h

theorem flags_begin (hn : 6 ≤ n) (hq0 : q0 ∈ Q) :
    List.ofFn (fun i : Fin n => decide (q0+i ∈ Q)) = true :: flags n Q q0 := by
  cases n with
  | zero => omega
  | succ m =>
    rw [List.ofFn_succ]
    have hf : decide (q0+0 ∈ Q) = true := by simpa using hq0
    rw [hf]
    congr 1
    simp only [flags, Nat.add_sub_cancel]
    apply congrArg List.ofFn
    funext i
    congr 2
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_succ, Fin.val_ofNat, Fin.val_cast]
    rw [Nat.mod_eq_of_lt (by have := i.isLt; omega : i.val+1 < m+1)]

theorem flags_admissible (hn : 6 ≤ n) (hq0 : q0 ∈ Q)
    (hsep : ∀ q ∈ Q, q+1 ∉ Q ∧ q+2 ∉ Q) :
    ∃ fs : List Bool,
      List.ofFn (fun i : Fin n => decide (q0+i ∈ Q)) = true :: fs ∧
      valid initial fs ∧ (run initial fs).2.1 = 0 ∧ (run initial fs).2.2 = 6 := by
  refine ⟨flags n Q q0, flags_begin n Q q0 hn hq0, ?_, ?_, ?_⟩
  · exact valid_of_separated initial _ (by simpa [initial] using flag_safe n Q q0 hn hq0 hsep) (flag_sep n Q q0 hn hsep)
  · have hsplit : flags n Q q0 = (flags n Q q0).take (n-3) ++ [false,false] := by
      rw [← flag_end n Q q0 hn hq0 hsep, List.take_append_drop]
    rw [hsplit]
    exact run_two_free_cool initial _ (by simp [initial])
  · rw [run_age initial _ (by simp [initial])]
    simp [initial, flags]
    omega
end In1081Flags

theorem op874_separated_defect_flags_are_admissible
    (n : ℕ) [NeZero n] (hn : 6 ≤ n) (Q : Finset (Fin n))
    (q0 : Fin n) (hq0 : q0 ∈ Q)
    (hsep : ∀ q ∈ Q, q + 1 ∉ Q ∧ q + 2 ∉ Q) :
    ∃ fs : List Bool,
      List.ofFn (fun i : Fin n => decide (q0+i ∈ Q)) = true :: fs ∧
      In1081Separated.valid In1081Separated.initial fs ∧
      (In1081Separated.run In1081Separated.initial fs).2.1 = 0 ∧
      (In1081Separated.run In1081Separated.initial fs).2.2 = 6 := by
  exact In1081Flags.flags_admissible n Q q0 hn hq0 hsep
