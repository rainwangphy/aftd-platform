import AFTD.Prelude
import AFTD.Kb.Tcs.Op874SeparatedWindowAutomatonAcceptance

/-!
# op874_separated_window_automaton_identity_path

Topic: graphs   Node: c9ef79c24007

Provenance: helper lemma. Semantic interpretation of the 26-state certificate for OP-874, experiment 35454.

For every admissible forced/free word with a first forced step, total length at least six and two free steps before closure, there is a sequence of actual three-color or four-color rotations returning the ordered four-color state to the identity.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Separated

abbrev Colors := Fin 4 × Fin 4 × Fin 4 × Fin 4

def colorStates : Array Colors := #[
  (0, 1, 2, 3),
  (0, 1, 3, 2),
  (0, 2, 1, 3),
  (0, 2, 3, 1),
  (0, 3, 1, 2),
  (0, 3, 2, 1),
  (1, 0, 2, 3),
  (1, 0, 3, 2),
  (1, 2, 0, 3),
  (1, 2, 3, 0),
  (1, 3, 0, 2),
  (1, 3, 2, 0),
  (2, 0, 1, 3),
  (2, 0, 3, 1),
  (2, 1, 0, 3),
  (2, 1, 3, 0),
  (2, 3, 0, 1),
  (2, 3, 1, 0),
  (3, 0, 1, 2),
  (3, 0, 2, 1),
  (3, 1, 0, 2),
  (3, 1, 2, 0),
  (3, 2, 0, 1),
  (3, 2, 1, 0)
]

def rotate3 (p : Colors) : Colors := (p.2.1, p.2.2.1, p.1, p.2.2.2)
def rotate4 (p : Colors) : Colors := (p.2.1, p.2.2.1, p.2.2.2, p.1)

theorem step3_colors (i : Fin 24) : colorStates[step3[i.val]!]! = rotate3 colorStates[i.val]! := by
  revert i
  decide

theorem step4_colors (i : Fin 24) : colorStates[step4[i.val]!]! = rotate4 colorStates[i.val]! := by
  revert i
  decide

theorem step3_lt (i : Fin 24) : step3[i.val]! < 24 := by
  revert i
  decide

theorem step4_lt (i : Fin 24) : step4[i.val]! < 24 := by
  revert i
  decide

theorem shift3_bit (i j : Fin 24) :
    (1 <<< step3[i.val]!).testBit j.val = true ↔ j.val = step3[i.val]! := by
  revert i j
  decide

theorem shift4_bit (i j : Fin 24) :
    (1 <<< step4[i.val]!).testBit j.val = true ↔ j.val = step4[i.val]! := by
  revert i j
  decide

end In1081Separated
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Separated

theorem fold_bits (xs : List Nat) (f : Nat → Nat) (z j : Nat) :
    (xs.foldl (fun a i => a ||| f i) z).testBit j =
      (z.testBit j || xs.any (fun i => (f i).testBit j)) := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.any_cons, Nat.testBit_lor]
    simp only [Bool.or_assoc]

theorem move_bits (mask : Nat) (forced : Bool) (j : Nat) :
    (move mask forced).testBit j =
      (List.range 24).any (fun i => mask.testBit i &&
        ((1 <<< step4[i]!).testBit j || (!forced && (1 <<< step3[i]!).testBit j))) := by
  unfold move
  have hfun : (fun out i => if mask.testBit i then
      out ||| (1 <<< step4[i]!) ||| (if forced then 0 else (1 <<< step3[i]!)) else out) =
      (fun out i => out ||| (if mask.testBit i then
        (1 <<< step4[i]!) ||| (if forced then 0 else (1 <<< step3[i]!)) else 0)) := by
    funext out i
    cases h : mask.testBit i <;> cases forced <;> simp [h, Nat.or_assoc]
  rw [hfun, fold_bits]
  simp only [Nat.zero_testBit, Bool.false_or]
  congr 1
  funext i
  cases h : mask.testBit i <;> cases forced <;> simp [h, Nat.testBit_lor]

def transition (forced : Bool) (i j : Fin 24) : Prop :=
  j.val = step4[i.val]! ∨ (forced = false ∧ j.val = step3[i.val]!)

theorem move_iff (mask : Nat) (forced : Bool) (j : Fin 24) :
    (move mask forced).testBit j.val = true ↔
      ∃ i : Fin 24, mask.testBit i.val = true ∧ transition forced i j := by
  rw [move_bits]
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨i, hi, hm, h⟩
    let ii : Fin 24 := ⟨i, hi⟩
    refine ⟨ii, hm, ?_⟩
    rcases h with h | ⟨hf, h⟩
    · exact Or.inl ((shift4_bit ii j).1 h)
    · have hf' : forced = false := by cases forced <;> simp_all
      exact Or.inr ⟨hf', (shift3_bit ii j).1 h⟩
  · rintro ⟨i, hm, h⟩
    refine ⟨i.val, i.isLt, hm, ?_⟩
    rcases h with h | ⟨hf, h⟩
    · exact Or.inl ((shift4_bit i j).2 h)
    · have hf' : (!forced) = true := by cases forced <;> simp_all
      exact Or.inr ⟨hf', (shift3_bit i j).2 h⟩
end In1081Separated
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Separated

def maskRun (mask : Nat) : List Bool → Nat
  | [] => mask
  | f :: fs => maskRun (move mask f) fs

def path (start : Fin 24) : List Bool → Fin 24 → Prop
  | [], finish => finish = start
  | f :: fs, finish => ∃ mid : Fin 24, transition f start mid ∧ path mid fs finish

theorem maskRun_iff (fs : List Bool) (mask : Nat) (finish : Fin 24) :
    (maskRun mask fs).testBit finish.val = true ↔
      ∃ start : Fin 24, mask.testBit start.val = true ∧ path start fs finish := by
  induction fs generalizing mask with
  | nil =>
    simp only [maskRun, path]
    constructor
    · intro h; exact ⟨finish, h, rfl⟩
    · rintro ⟨start, hs, rfl⟩; exact hs
  | cons f fs ih =>
    simp only [maskRun, ih, move_iff, path]
    constructor
    · rintro ⟨mid, ⟨start, hs, hstep⟩, hpath⟩
      exact ⟨start, hs, mid, hstep, hpath⟩
    · rintro ⟨start, hs, mid, hstep, hpath⟩
      exact ⟨mid, ⟨start, hs, hstep⟩, hpath⟩

theorem run_mask (s : S) (fs : List Bool) : (run s fs).1 = maskRun s.1 fs := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih =>
    cases f <;> simpa [run, maskRun, freeStep, forcedStep] using ih _

theorem initial_bit (i : Fin 24) : initial.1.testBit i.val = true ↔ i.val = 9 := by
  revert i
  decide

theorem forced_first_transition : transition true (0 : Fin 24) (9 : Fin 24) := by
  unfold transition
  left
  decide

theorem admissible_run_has_identity_path (fs : List Bool) (hv : valid initial fs)
    (hc : (run initial fs).2.1 = 0) (ha : (run initial fs).2.2 = 6) :
    path (0 : Fin 24) (true :: fs) (0 : Fin 24) := by
  have hbit := admissible_run_accepts fs hv hc ha
  rw [run_mask] at hbit
  obtain ⟨start, hs, hp⟩ := (maskRun_iff fs initial.1 0).1 hbit
  have hstart : start = (9 : Fin 24) := Fin.ext ((initial_bit start).1 hs)
  subst start
  exact ⟨9, forced_first_transition, hp⟩
end In1081Separated
open In1081Separated

theorem op874_separated_window_automaton_identity_path
    (fs : List Bool) (hv : valid initial fs)
    (hc : (run initial fs).2.1 = 0) (ha : (run initial fs).2.2 = 6) :
    path (0 : Fin 24) (true :: fs) (0 : Fin 24) := by
  exact admissible_run_has_identity_path fs hv hc ha
