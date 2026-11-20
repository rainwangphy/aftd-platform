import AFTD.Prelude
import AFTD.Kb.Tcs.Op874SeparatedDefectFlagsAreAdmissible
import AFTD.Kb.Tcs.Op874SeparatedWindowAutomatonIdentityPath
import AFTD.Kb.Tcs.Op874AutomatonIdentityPathGivesPaletteStates
import AFTD.Kb.Tcs.Op874PaletteStateCycleGivesFourWindows
import AFTD.Kb.Tcs.Op874SeparatedWindowAutomatonAcceptance

/-!
# op874_separated_defects_square_cycle_four_windows

Topic: graphs   Node: fd2521e61b3b

Provenance: helper lemma. Candidate repair of the OP-874 producer-cycle route, experiments 35451 and 35454.

For every cycle of length at least six and nonempty defect set with circular spacing at least three, there is a square-proper four-color edge word whose four-edge window around each defect uses all four colors.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
open In1081Separated

theorem in1081_separated_finish
    (n : ℕ) [NeZero n] (hn : 6 ≤ n) (Q : Finset (Fin n)) (hne : Q.Nonempty)
    (hf : ∀ q0 ∈ Q, ∃ fs : List Bool,
      List.ofFn (fun i : Fin n => decide (q0+i ∈ Q)) = true :: fs ∧
      valid initial fs ∧ (run initial fs).2.1 = 0 ∧ (run initial fs).2.2 = 6) :
    ∃ c : Fin n → Fin 4,
      (∀ i, c i ≠ c (i+1) ∧ c i ≠ c (i+2)) ∧
      (∀ q ∈ Q, [c (q-2), c (q-1), c q, c (q+1)].Nodup) := by
  obtain ⟨q0, hq0⟩ := hne
  obtain ⟨fs, hflags, hv, hc, ha⟩ := hf q0 hq0
  have hp := op874_separated_window_automaton_identity_path fs hv hc ha
  rw [← hflags] at hp
  obtain ⟨t, ht⟩ := op874_automaton_identity_path_gives_palette_states n hn
    (fun i => decide (q0+i ∈ Q)) hp
  let s : Fin n → Equiv.Perm (Fin 4) := fun j => t (j+2-q0)
  have hsum : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    simp only [Fin.val_add]
    change (1 % n + 1 % n) % n = 2 % n
    rw [Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt (by omega : 2 < n)]
  apply op874_palette_state_cycle_gives_four_windows n hn Q s
  · intro j
    have he : (j+1)+2-q0 = (j+2-q0)+1 := by abel
    simpa only [s, he] using ⟨(ht (j+2-q0)).1, (ht (j+2-q0)).2.1⟩
  · intro q hq
    let i : Fin n := q-q0
    have hfq : decide (q0+i ∈ Q) = true := by
      have he : q0+i=q := by dsimp [i]; abel
      simp only [he, decide_eq_true_eq]; exact hq
    have hforced := (ht i).2.2 hfq
    have ha1 := (ht (i+1)).2.1
    have ha2 := (ht (i+1+1)).1
    have he1 : (q+1)+2-q0 = i+1+1+1 := by dsimp [i]; rw [← hsum]; abel
    have he2 : (q-2)+2-q0 = i := by dsimp [i]; abel
    change t ((q+1)+2-q0) 0 = t ((q-2)+2-q0) 3
    rw [he1, he2]
    calc
      t (i+1+1+1) 0 = t (i+1+1) 1 := ha2
      _ = t (i+1) 2 := ha1
      _ = t i 3 := hforced

theorem op874_separated_defects_square_cycle_four_windows
    (n : ℕ) [NeZero n] (hn : 6 ≤ n) (Q : Finset (Fin n)) (hne : Q.Nonempty)
    (hsep : ∀ q ∈ Q, q + 1 ∉ Q ∧ q + 2 ∉ Q) :
    ∃ c : Fin n → Fin 4,
      (∀ i, c i ≠ c (i+1) ∧ c i ≠ c (i+2)) ∧
      (∀ q ∈ Q, [c (q-2), c (q-1), c q, c (q+1)].Nodup) := by
  exact in1081_separated_finish n hn Q hne
    (fun q hq => op874_separated_defect_flags_are_admissible n hn Q q hq hsep)
