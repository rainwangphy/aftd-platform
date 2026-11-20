import AFTD.Prelude

/-!
# op874_six_cycle_two_defect_four_window_obstruction

Topic: graphs   Node: c7f92ccf7bf5

Provenance: helper lemma. Explicit obstruction to the OP-874 multi-defect square-proper producer route, experiment 35407.

On a six-cycle, no square-proper word in four colors can have four distinct colors in both edge windows 0–3 and 2–5. Thus the fixed pair of nonadjacent defect vertices 2 and 4 cannot both satisfy the proposed predecessor-demand four-window condition.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
theorem in1081_six_colors_two_windows_impossible
    (a b c d e f : Fin 4)
    (hleft : [a,b,c,d].Nodup) (hright : [c,d,e,f].Nodup)
    (he : e ≠ a) (hf : f ≠ a) : False := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at hleft hright
  simp only [Fin.ext_iff] at *
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have he' := e.isLt
  have hf' := f.isLt
  omega

theorem op874_six_cycle_two_defect_four_window_obstruction
    (c : Fin 6 → Fin 4)
    (hsquare : ∀ i, c i ≠ c (i+1) ∧ c i ≠ c (i+2))
    (hleft : [c 0, c 1, c 2, c 3].Nodup)
    (hright : [c 2, c 3, c 4, c 5].Nodup) : False := by
  apply in1081_six_colors_two_windows_impossible (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) hleft hright
  · simpa using (hsquare 4).2
  · simpa using (hsquare 5).1
