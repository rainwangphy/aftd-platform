import AFTD.Prelude

/-!
# op309_source_forest_odd_cycle_kernel

Topic: graphs   Node: 4be30ab3b1da

Provenance: helper lemma. OP-309 source-forest quotient obstruction, experiments 42290 and 42300.

Three pairwise distinct colors adjacent to every vertex of a five-cycle cannot coexist with a proper five-coloring of that cycle.
-/

theorem op309_source_forest_odd_cycle_kernel (a b c d e f g h : Fin 5)
    (h01 : a ≠ b)
    (h02 : a ≠ c)
    (h12 : b ≠ c)
    (h03 : a ≠ d)
    (h04 : a ≠ e)
    (h05 : a ≠ f)
    (h06 : a ≠ g)
    (h07 : a ≠ h)
    (h13 : b ≠ d)
    (h14 : b ≠ e)
    (h15 : b ≠ f)
    (h16 : b ≠ g)
    (h17 : b ≠ h)
    (h23 : c ≠ d)
    (h24 : c ≠ e)
    (h25 : c ≠ f)
    (h26 : c ≠ g)
    (h27 : c ≠ h)
    (h34 : d ≠ e)
    (h45 : e ≠ f)
    (h56 : f ≠ g)
    (h67 : g ≠ h)
    (h73 : h ≠ d) : False := by
  have hdf : d = f := by
    by_contra hdfne
    have hn : [a,b,c,d,e,f].Nodup := by
      have k01 : a ≠ b := h01
      have k02 : a ≠ c := h02
      have k03 : a ≠ d := h03
      have k04 : a ≠ e := h04
      have k05 : a ≠ f := h05
      have k12 : b ≠ c := h12
      have k13 : b ≠ d := h13
      have k14 : b ≠ e := h14
      have k15 : b ≠ f := h15
      have k23 : c ≠ d := h23
      have k24 : c ≠ e := h24
      have k25 : c ≠ f := h25
      have k34 : d ≠ e := h34
      have k35 : d ≠ f := hdfne
      have k45 : e ≠ f := h45
      simp [k01, k02, k03, k04, k05, k12, k13, k14, k15, k23, k24, k25, k34, k35, k45]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  have heg : e = g := by
    by_contra hegne
    have hdg : d ≠ g := by
      rw [hdf]
      exact h56
    have hn : [a,b,c,d,e,g].Nodup := by
      have k01 : a ≠ b := h01
      have k02 : a ≠ c := h02
      have k03 : a ≠ d := h03
      have k04 : a ≠ e := h04
      have k06 : a ≠ g := h06
      have k12 : b ≠ c := h12
      have k13 : b ≠ d := h13
      have k14 : b ≠ e := h14
      have k16 : b ≠ g := h16
      have k23 : c ≠ d := h23
      have k24 : c ≠ e := h24
      have k26 : c ≠ g := h26
      have k34 : d ≠ e := h34
      have k36 : d ≠ g := hdg
      have k46 : e ≠ g := hegne
      simp [k01, k02, k03, k04, k06, k12, k13, k14, k16, k23, k24, k26, k34, k36, k46]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  have hdh : d ≠ h := Ne.symm h73
  have heh : e ≠ h := by
    rw [heg]
    exact h67
  have hn : [a,b,c,d,e,h].Nodup := by
      have k01 : a ≠ b := h01
      have k02 : a ≠ c := h02
      have k03 : a ≠ d := h03
      have k04 : a ≠ e := h04
      have k07 : a ≠ h := h07
      have k12 : b ≠ c := h12
      have k13 : b ≠ d := h13
      have k14 : b ≠ e := h14
      have k17 : b ≠ h := h17
      have k23 : c ≠ d := h23
      have k24 : c ≠ e := h24
      have k27 : c ≠ h := h27
      have k34 : d ≠ e := h34
      have k37 : d ≠ h := hdh
      have k47 : e ≠ h := heh
      simp [k01, k02, k03, k04, k07, k12, k13, k14, k17, k23, k24, k27, k34, k37, k47]
  have hc := List.Nodup.length_le_card hn
  norm_num at hc
