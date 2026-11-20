import AFTD.Prelude

/-!
# op874_separated_window_automaton_acceptance

Topic: graphs   Node: 13b346b037c7

Provenance: helper lemma. Twenty-six-state finite certificate for the OP-874 separated-defect four-window route, experiment 35454.

In the explicit 24-permutation subset automaton, every admissible forced/free run that reaches length at least six and has two free positions before cyclic closure contains the identity state.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Separated

def step3 : Array Nat := #[8,10,14,16,20,22,2,4,12,17,18,23,0,5,6,11,19,21,1,3,7,9,13,15]
def step4 : Array Nat := #[9,11,15,17,21,23,3,5,13,16,19,22,1,4,7,10,18,20,0,2,6,8,12,14]
def move (mask : Nat) (forced : Bool) : Nat :=
  (List.range 24).foldl (fun out i =>
    if mask.testBit i then out ||| (1 <<< step4[i]!) ||| (if forced then 0 else (1 <<< step3[i]!)) else out) 0

abbrev S := Nat × Nat × Nat
def freeStep (s : S) : S := (move s.1 false, s.2.1 - 1, min 6 (s.2.2 + 1))
def forcedStep (s : S) : S := (move s.1 true, 2, min 6 (s.2.2 + 1))
def initial : S := (512, 2, 1)
def certificate : List S := [
  (325, 2, 4),
  (512, 2, 1),
  (975, 0, 4),
  (62220, 1, 5),
  (196608, 1, 2),
  (240168, 2, 5),
  (261363, 0, 6),
  (261948, 0, 5),
  (262143, 0, 6),
  (262143, 2, 6),
  (3932160, 0, 3),
  (3997695, 1, 6),
  (15465325, 2, 6),
  (15466495, 2, 6),
  (16518842, 2, 6),
  (16519167, 0, 6),
  (16539647, 2, 6),
  (16577487, 0, 6),
  (16580607, 0, 6),
  (16714800, 1, 6),
  (16753810, 2, 6),
  (16756410, 2, 6),
  (16776435, 0, 6),
  (16777215, 0, 6),
  (16777215, 1, 6),
  (16777215, 2, 6)
]

def goodState (s : S) : Bool :=
  (if s.2.2 = 6 ∧ s.2.1 = 0 then s.1.testBit 0 else true) &&
  certificate.contains (freeStep s) &&
  (if s.2.1 = 0 then certificate.contains (forcedStep s) else true)

theorem initial_in_certificate : initial ∈ certificate := by decide
theorem certificate_checked : certificate.all goodState = true := by decide

end In1081Separated
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Separated

theorem checked_of_mem (s : S) (hs : s ∈ certificate) : goodState s = true :=
  (List.all_eq_true.mp certificate_checked) s hs

theorem free_closed (s : S) (hs : s ∈ certificate) : freeStep s ∈ certificate := by
  have h := checked_of_mem s hs
  simp only [goodState, Bool.and_eq_true] at h
  simpa using h.1.2

theorem forced_closed (s : S) (hs : s ∈ certificate) (hc : s.2.1 = 0) :
    forcedStep s ∈ certificate := by
  have h := checked_of_mem s hs
  simp only [goodState, Bool.and_eq_true, hc, if_true] at h
  simpa using h.2

theorem accepted_of_mem (s : S) (hs : s ∈ certificate)
    (hc : s.2.1 = 0) (ha : s.2.2 = 6) : s.1.testBit 0 = true := by
  have h := checked_of_mem s hs
  simp only [goodState, Bool.and_eq_true, hc, ha, and_self, if_true] at h
  exact h.1.1

def run (s : S) : List Bool → S
  | [] => s
  | f :: fs => run (if f then forcedStep s else freeStep s) fs

def valid (s : S) : List Bool → Prop
  | [] => True
  | f :: fs => (f = true → s.2.1 = 0) ∧
      valid (if f then forcedStep s else freeStep s) fs

theorem run_closed (s : S) (hs : s ∈ certificate) (fs : List Bool)
    (hv : valid s fs) : run s fs ∈ certificate := by
  induction fs generalizing s with
  | nil => exact hs
  | cons f fs ih =>
    cases f with
    | false =>
      exact ih (freeStep s) (free_closed s hs) hv.2
    | true =>
      exact ih (forcedStep s) (forced_closed s hs (hv.1 rfl)) hv.2

theorem admissible_run_accepts (fs : List Bool) (hv : valid initial fs)
    (hc : (run initial fs).2.1 = 0) (ha : (run initial fs).2.2 = 6) :
    (run initial fs).1.testBit 0 = true :=
  accepted_of_mem _ (run_closed initial initial_in_certificate fs hv) hc ha
end In1081Separated
open In1081Separated

theorem op874_separated_window_automaton_acceptance
    (fs : List Bool) (hv : valid initial fs)
    (hc : (run initial fs).2.1 = 0) (ha : (run initial fs).2.2 = 6) :
    (run initial fs).1.testBit 0 = true := by
  exact admissible_run_accepts fs hv hc ha
