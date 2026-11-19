import AFTD.Prelude

/-!
# six_cycle_three_pairs_outer_inequalities_contradiction

Topic: combinatorics   Node: 7a9742f9b6fc

Provenance: helper lemma. Six-cycle palette kernel for the OP-874 nonbinary ownership obstruction.

On six cyclic colors, if one color occurs in three alternating incident pairs, then the stated outer-color inequalities cannot both hold.
-/

theorem six_cycle_three_pairs_outer_inequalities_contradiction
    {Ω : Type*} (a b c d e f z : Ω)
    (h1 : z = a ∨ z = b) (h2 : z = c ∨ z = d) (h3 : z = e ∨ z = f)
    (hfa : f ≠ a) (hbc : b ≠ c) (hde : d ≠ e)
    (hac : a ≠ c) (hbf : b ≠ f) : False := by
  rcases h1 with hza | hzb
  · have hzf : z ≠ f := by
      intro hz
      exact hfa (hz.symm.trans hza)
    have hze : z = e := h3.resolve_right hzf
    have hzd : z ≠ d := by
      intro hz
      exact hde (hz.symm.trans hze)
    have hzc : z = c := h2.resolve_right hzd
    exact hac (hza.symm.trans hzc)
  · have hzc : z ≠ c := by
      intro hz
      exact hbc (hzb.symm.trans hz)
    have hzd : z = d := h2.resolve_left hzc
    have hze : z ≠ e := by
      intro hz
      exact hde (hzd.symm.trans hz)
    have hzf : z = f := h3.resolve_left hze
    exact hbf (hzb.symm.trans hzf)
