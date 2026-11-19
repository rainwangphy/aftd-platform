import AFTD.Prelude
import AFTD.Kb.Tcs.OverlappingFiveWindowsForceMiddlePair

/-!
# six_cycle_three_path_four_color_windows_obstruction

Topic: graphs   Node: 5e3e56d6130f

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign; the concrete instance is independently checked in experiments 33309, 33310, 33320, 33321 and 33322.

Six colors around a six-cycle cannot satisfy the three specified pair-separation inequalities and have every one of four colors in each of the two specified five-position windows.
-/

theorem six_cycle_three_path_four_color_windows_obstruction
    (a b c d e f : Fin 4)
    (hde : d ≠ e) (hef : e ≠ f) (hfa : f ≠ a)
    (h_mono_de : ({d, e} : Finset (Fin 4)) ≠ {e, f})
    (h_mono_fa : ({e, f} : Finset (Fin 4)) ≠ {f, a})
    (h_match : ({b, c} : Finset (Fin 4)) ≠ {e, f})
    (h_window_left : ∀ x : Fin 4, x ∈ ({f, a, b, c, d} : Finset (Fin 4)))
    (h_window_right : ∀ x : Fin 4, x ∈ ({a, b, c, d, e} : Finset (Fin 4))) :
    False := by
  have hed : e ≠ d := Ne.symm hde
  have hfd : f ≠ d := by
    intro h
    apply h_mono_de
    rw [h]
    exact Finset.pair_comm _ _
  have hea : e ≠ a := by
    intro h
    apply h_mono_fa
    rw [h]
    exact Finset.pair_comm _ _
  apply h_match
  exact overlapping_five_windows_force_middle_pair a b c d e f hea hed hef hfa hfd
    (h_window_left e) (h_window_right f)
