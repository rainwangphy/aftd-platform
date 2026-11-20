import AFTD.Prelude
import AFTD.Kb.Tcs.Op874SeparatedWindowAutomatonAcceptance

/-!
# op874_separated_word_automaton_safety

Topic: graphs   Node: d2e44d78f9b4

Provenance: helper lemma. Spacing-to-automaton transfer for the OP-874 separated-defect construction.

For the separated-defect automaton, a finite Boolean word is valid if no two forced positions are one or two indices apart and its opening positions respect the current cooldown.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Separated

def safePrefix (k : Nat) (fs : List Bool) : Prop :=
  ∀ i, i < k → fs[i]? ≠ some true

def separated (fs : List Bool) : Prop :=
  ∀ i, fs[i]? = some true → fs[i+1]? ≠ some true ∧ fs[i+2]? ≠ some true

theorem separated_tail (f : Bool) (fs : List Bool) (h : separated (f :: fs)) : separated fs := by
  intro i hi
  have hh := h (i+1) (by simpa using hi)
  simpa [Nat.add_assoc] using hh

theorem valid_of_separated (s : S) (fs : List Bool)
    (hsafe : safePrefix s.2.1 fs) (hsep : separated fs) : valid s fs := by
  induction fs generalizing s with
  | nil => trivial
  | cons f fs ih =>
    have htail : separated fs := separated_tail f fs hsep
    cases f with
    | false =>
      have hsafe' : safePrefix (freeStep s).2.1 fs := by
        intro i hi
        have hlt : i+1 < s.2.1 := by
          change i < s.2.1 - 1 at hi
          omega
        have hh := hsafe (i+1) hlt
        simpa using hh
      exact ⟨by simp, ih (freeStep s) hsafe' htail⟩
    | true =>
      have hc : s.2.1 = 0 := by
        by_contra hn
        have hh := hsafe 0 (by omega)
        simp at hh
      have hsafe' : safePrefix (forcedStep s).2.1 fs := by
        intro i hi
        change i < 2 at hi
        have hh := hsep 0 (by simp)
        interval_cases i
        · simpa using hh.1
        · simpa using hh.2
      exact ⟨fun _ => hc, ih (forcedStep s) hsafe' htail⟩

theorem run_append (s : S) (xs ys : List Bool) : run s (xs ++ ys) = run (run s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simpa [run] using ih (if x then forcedStep s else freeStep s)

theorem run_age (s : S) (fs : List Bool) (hs : s.2.2 ≤ 6) :
    (run s fs).2.2 = min 6 (s.2.2 + fs.length) := by
  induction fs generalizing s with
  | nil => simp [run, Nat.min_eq_right hs]
  | cons x xs ih =>
    cases x with
    | false =>
      change (run (freeStep s) xs).2.2 = _
      rw [ih (freeStep s) (by simp [freeStep] <;> omega)]
      simp only [freeStep, List.length_cons]
      omega
    | true =>
      change (run (forcedStep s) xs).2.2 = _
      rw [ih (forcedStep s) (by simp [forcedStep] <;> omega)]
      simp only [forcedStep, List.length_cons]
      omega

theorem run_cool_bound (s : S) (fs : List Bool) (hs : s.2.1 ≤ 2) :
    (run s fs).2.1 ≤ 2 := by
  induction fs generalizing s with
  | nil => exact hs
  | cons x xs ih =>
    cases x with
    | false => exact ih (freeStep s) (by simp [freeStep] <;> omega)
    | true => exact ih (forcedStep s) (by simp [forcedStep])

theorem run_two_free_cool (s : S) (fs : List Bool) (hs : s.2.1 ≤ 2) :
    (run s (fs ++ [false, false])).2.1 = 0 := by
  have hb := run_cool_bound s fs hs
  rw [run_append]
  simp [run, freeStep]
  omega
end In1081Separated
open In1081Separated

theorem op874_separated_word_automaton_safety (s : S) (fs : List Bool)
    (hsafe : safePrefix s.2.1 fs) (hsep : separated fs) : valid s fs := by
  exact valid_of_separated s fs hsafe hsep
