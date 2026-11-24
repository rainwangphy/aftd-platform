import AFTD.Prelude

/-!
# matching_short_alternating_cycle_near_universal

Topic: graphs   Node: c89cac735c45

Provenance: helper lemma. OP-1957: a 4- or 6-vertex repair for near-universal vertices in the residual graph.

In a simple graph in which every vertex has at least two neighbors, let P be a perfect matching, let uv be a matching edge, and suppose u has at most one nonneighbor other than itself. Then uv lies on a P-alternating cycle of length four or six, with distinct vertices and matching edges as displayed.
-/

private lemma matching_short_alternating_cycle_near_universal_inj4
    {V : Type*} {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a,b,c,d] : Fin 4 → V) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private lemma matching_short_alternating_cycle_near_universal_inj6
    {V : Type*} {a b c d e f : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    Function.Injective (![a,b,c,d,e,f] : Fin 6 → V) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem matching_short_alternating_cycle_near_universal
    {V : Type*} (G : SimpleGraph V) (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (hdeg : ∀ x : V, ∃ a b : V, a ≠ b ∧ G.Adj x a ∧ G.Adj x b)
    (u v : V) (huv : P.Adj u v)
    (hnear : ∀ a b : V, a ≠ u → b ≠ u → ¬ G.Adj u a → ¬ G.Adj u b → a = b) :
    (∃ a b : V, Function.Injective (![u,v,a,b] : Fin 4 → V) ∧ P.Adj a b ∧ G.Adj v a ∧ G.Adj u b) ∨
    (∃ a b c d : V, Function.Injective (![u,v,a,b,c,d] : Fin 6 → V) ∧ P.Adj a b ∧ P.Adj c d ∧ G.Adj v b ∧ G.Adj a c ∧ G.Adj u d) := by
  classical
  have hM : P.IsMatching := hP.1
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hP
  let m : V → V := fun x => (hP x).choose
  have hm_adj : ∀ x : V, P.Adj x (m x) := fun x => (hP x).choose_spec.1
  have hm_eq : ∀ {x y : V}, P.Adj x y → y = m x := fun {x y} hxy => (hP x).choose_spec.2 y hxy
  have hm_u : m u = v := (hm_eq huv).symm
  have hm_v : m v = u := (hm_eq huv.symm).symm
  have huv_ne : u ≠ v := (P.adj_sub huv).ne
  have hvu_ne : v ≠ u := huv_ne.symm
  have adj_u_of_ne_nonneighbor : ∀ {z x : V}, z ≠ u → x ≠ z → x ≠ u → ¬ G.Adj u z → G.Adj u x := by
    intro z x hz hxz hxu hnz
    by_contra hx
    have hxz_eq : x = z := hnear x z hxu hz hx hnz
    exact hxz hxz_eq
  obtain ⟨r, s, hrs, hvr, hvs⟩ := hdeg v
  have hex : ∃ w : V, G.Adj v w ∧ w ≠ u := by
    by_cases hr : r = u
    · exact ⟨s, hvs, fun hs => hrs (hr.trans hs.symm)⟩
    · exact ⟨r, hvr, hr⟩
  obtain ⟨w, hvw, hwu⟩ := hex
  let z : V := m w
  have hPwz : P.Adj w z := by simpa [z] using hm_adj w
  have hPzw : P.Adj z w := hPwz.symm
  have hwz_ne : w ≠ z := (P.adj_sub hPwz).ne
  have hzu : z ≠ u := by
    intro hz
    have hPwu : P.Adj w u := by simpa [hz] using hPwz
    have hPuw : P.Adj u w := hPwu.symm
    exact (hM.not_adj_left_of_ne (G.ne_of_adj hvw) huv) hPuw
  have hzv : z ≠ v := by
    intro hz
    have hPwv : P.Adj w v := by simpa [hz] using hPwz
    have hPvw : P.Adj v w := hPwv.symm
    have huw : u ≠ w := hwu.symm
    exact (hM.not_adj_left_of_ne huw huv.symm) hPvw
  have hzw : z ≠ w := hwz_ne.symm
  have hwv : w ≠ v := (G.ne_of_adj hvw).symm
  by_cases hcase : G.Adj u z
  · left
    refine ⟨w, z, ?_, hPwz, hvw, hcase⟩
    exact matching_short_alternating_cycle_near_universal_inj4 huv_ne hwu.symm hzu.symm hwv.symm hzv.symm hwz_ne
  · have huw : G.Adj u w := adj_u_of_ne_nonneighbor hzu hwz_ne hwu hcase
    obtain ⟨r, s, hrs, hzr, hzs⟩ := hdeg z
    have hexc : ∃ c : V, G.Adj z c ∧ c ≠ w := by
      by_cases hrw : r = w
      · exact ⟨s, hzs, fun hs => hrs (hrw.trans hs.symm)⟩
      · exact ⟨r, hzr, hrw⟩
    obtain ⟨c, hzc, hcw⟩ := hexc
    have hcu : c ≠ u := by
      intro hcu
      exact hcase (by simpa [hcu] using hzc.symm)
    by_cases hcv : c = v
    · left
      refine ⟨z, w, ?_, hPzw, ?_, huw⟩
      · exact matching_short_alternating_cycle_near_universal_inj4 huv_ne hzu.symm hwu.symm hzv.symm hwv.symm hzw
      · simpa [hcv] using hzc.symm
    · right
      let d : V := m c
      have hPcd : P.Adj c d := by simpa [d] using hm_adj c
      have hdc : d ≠ c := (P.adj_sub hPcd).ne.symm
      have hdz : d ≠ z := by
        intro hdz
        have hPcz : P.Adj c z := by simpa [hdz] using hPcd
        have hcw_eq : c = w := hM.eq_of_adj_right hPcz hPwz
        exact hcw hcw_eq
      have hdu : d ≠ u := by
        intro hdu
        have hPcu : P.Adj c u := by simpa [hdu] using hPcd
        have hcv_eq : c = v := hM.eq_of_adj_right hPcu huv.symm
        exact hcv hcv_eq
      have hdv : d ≠ v := by
        intro hdv
        have hPcv : P.Adj c v := by simpa [hdv] using hPcd
        have hcu_eq : c = u := hM.eq_of_adj_right hPcv huv
        exact hcu hcu_eq
      have hdw : d ≠ w := by
        intro hdw
        have hPcw : P.Adj c w := by simpa [hdw] using hPcd
        have hcz_eq : c = z := hM.eq_of_adj_right hPcw hPzw
        exact (G.ne_of_adj hzc) hcz_eq.symm
      have hcz : c ≠ z := (G.ne_of_adj hzc).symm
      have hvc : v ≠ c := fun hvc => hcv hvc.symm
      have hud : G.Adj u d := adj_u_of_ne_nonneighbor hzu hdz hdu hcase
      refine ⟨z, w, c, d, ?_, hPzw, hPcd, hvw, hzc, hud⟩
      exact matching_short_alternating_cycle_near_universal_inj6
        huv_ne hzu.symm hwu.symm hcu.symm hdu.symm
        hzv.symm hwv.symm hvc hdv.symm
        hzw hcz.symm hdz.symm hcw.symm hdw.symm hdc.symm
