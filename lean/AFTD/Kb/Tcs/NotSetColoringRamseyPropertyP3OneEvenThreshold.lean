import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyProperty
import AFTD.Kb.Tcs.SupportGraph

/-!
# not_set_coloring_ramsey_property_p3_one_even_threshold

Topic: combinatorics   Node: 22cdadcf1fae

Provenance: helper lemma. arXiv:2611.15376 Lemma 2.1

For all integers a ≥ b ≥ 1, there exists an (a, b)-set-coloring of the complete graph on 2 * ⌊(a + b) / (2 * b)⌋ vertices without a monochromatic two-edge path P_3 in any single color.
-/

private lemma not_set_coloring_ramsey_property_p3_one_even_threshold_no_p3_of_adj_unique {W : Type*} {H : SimpleGraph W}
    (h : ∀ v x y, H.Adj v x → H.Adj v y → x = y) :
    ¬ (SimpleGraph.pathGraph 3).IsContained H := by
  rintro ⟨copy⟩
  have h01 : (SimpleGraph.pathGraph 3).Adj (⟨0, by norm_num⟩ : Fin 3) ⟨1, by norm_num⟩ := by
    rw [SimpleGraph.pathGraph_adj]; left; simp
  have h12 : (SimpleGraph.pathGraph 3).Adj (⟨1, by norm_num⟩ : Fin 3) ⟨2, by norm_num⟩ := by
    rw [SimpleGraph.pathGraph_adj]; left; simp
  have e1 : H.Adj (copy.toHom ⟨0, by norm_num⟩) (copy.toHom ⟨1, by norm_num⟩) := copy.toHom.map_adj h01
  have e2 : H.Adj (copy.toHom ⟨1, by norm_num⟩) (copy.toHom ⟨2, by norm_num⟩) := copy.toHom.map_adj h12
  have eq : copy.toHom ⟨0, by norm_num⟩ = copy.toHom ⟨2, by norm_num⟩ := h _ _ _ e1.symm e2
  have hfin : (⟨0, by norm_num⟩ : Fin 3) = ⟨2, by norm_num⟩ := copy.injective' eq
  norm_num at hfin

private def not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx (m : ℕ) (x y : Fin (2*m)) : ZMod (2*m-1) :=
  if x.val = 2*m-1 then
    (if y.val = 2*m-1 then 0 else (y.val : ZMod (2*m-1)))
  else
    (if y.val = 2*m-1 then (x.val : ZMod (2*m-1))
     else ((x.val : ZMod (2*m-1)) + (y.val : ZMod (2*m-1))) * (m : ZMod (2*m-1)))

private lemma not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx_comm (m : ℕ) (x y : Fin (2*m)) :
    not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m x y =
    not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m y x := by
  unfold not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx
  by_cases hx : x.val = 2*m-1 <;> by_cases hy : y.val = 2*m-1 <;>
    simp [hx, hy]
  ring

private lemma not_set_coloring_ramsey_property_p3_one_even_threshold_zmod_natcast_eq_of_lt {n : ℕ} [NeZero n] {p q : ℕ}
    (hp : p < n) (hq : q < n) (h : (p : ZMod n) = (q : ZMod n)) : p = q := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq] at this

private noncomputable def not_set_coloring_ramsey_property_p3_one_even_threshold_rrG (a b m : ℕ) (hb : 1 ≤ b) (hm : 1 ≤ m)
    (hbm : b * (2*m - 1) ≤ a) (s : Sym2 (Fin (2*m))) : Finset (Fin a) :=
  letI : NeZero (2*m-1) := ⟨by omega⟩
  (Finset.univ : Finset (Fin b)).image (fun j : Fin b =>
    ⟨b * (Sym2.lift ⟨not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m,
        not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx_comm m⟩ s).val + j.val, by
      have hB : (Sym2.lift ⟨not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m,
          not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx_comm m⟩ s).val < 2*m-1 := ZMod.val_lt _
      have hj : j.val < b := j.isLt
      have step : b * (Sym2.lift ⟨not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m,
              not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx_comm m⟩ s).val + j.val
          < b * ((Sym2.lift ⟨not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m,
              not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx_comm m⟩ s).val + 1) := by
        rw [Nat.mul_succ]; omega
      have step2 : b * ((Sym2.lift ⟨not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m,
              not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx_comm m⟩ s).val + 1) ≤ b * (2*m-1) :=
        Nat.mul_le_mul_left b (by omega)
      exact lt_of_lt_of_le (lt_of_lt_of_le step step2) hbm⟩)

private lemma not_set_coloring_ramsey_property_p3_one_even_threshold_rrG_card (a b m : ℕ) (hb : 1 ≤ b) (hm : 1 ≤ m)
    (hbm : b * (2*m - 1) ≤ a) (s : Sym2 (Fin (2*m))) :
    (not_set_coloring_ramsey_property_p3_one_even_threshold_rrG a b m hb hm hbm s).card = b := by
  unfold not_set_coloring_ramsey_property_p3_one_even_threshold_rrG
  letI : NeZero (2*m-1) := ⟨by omega⟩
  rw [Finset.card_image_of_injective _ ?inj, Finset.card_univ, Fintype.card_fin]
  intro j1 j2 h
  simp only [Fin.mk.injEq] at h
  have h1 : j1.val < b := j1.isLt
  have h2 : j2.val < b := j2.isLt
  omega

private lemma not_set_coloring_ramsey_property_p3_one_even_threshold_rrG_mem (a b m : ℕ) (hb : 1 ≤ b) (hm : 1 ≤ m)
    (hbm : b * (2*m - 1) ≤ a) (s : Sym2 (Fin (2*m))) (c : Fin a) :
    c ∈ not_set_coloring_ramsey_property_p3_one_even_threshold_rrG a b m hb hm hbm s ↔
      (Sym2.lift ⟨not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m,
        not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx_comm m⟩ s).val = c.val / b := by
  unfold not_set_coloring_ramsey_property_p3_one_even_threshold_rrG
  letI : NeZero (2*m-1) := ⟨by omega⟩
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hjmem, hjc⟩
    have hj : j.val < b := j.isLt
    have hval : b * (Sym2.lift ⟨not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m,
          not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx_comm m⟩ s).val + j.val = c.val := by
      have := congrArg Fin.val hjc
      simpa using this
    rw [← hval, Nat.mul_add_div (by omega : 0 < b), Nat.div_eq_of_lt hj, Nat.add_zero]
  · intro hc
    refine ⟨⟨c.val % b, Nat.mod_lt _ (by omega)⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp only
    rw [hc, Nat.div_add_mod]

private noncomputable def not_set_coloring_ramsey_property_p3_one_even_threshold_rrPhi (a b m : ℕ) (hb : 1 ≤ b) (hm : 1 ≤ m)
    (hbm : b * (2*m - 1) ≤ a) :
    (⊤ : SimpleGraph (Fin (2*m))).edgeSet → Finset (Fin a) :=
  fun e => not_set_coloring_ramsey_property_p3_one_even_threshold_rrG a b m hb hm hbm (e : Sym2 (Fin (2*m)))

private lemma not_set_coloring_ramsey_property_p3_one_even_threshold_rr_adj (a b m : ℕ) (hb : 1 ≤ b) (hm : 1 ≤ m)
    (hbm : b * (2*m - 1) ≤ a) (c : Fin a) (v x : Fin (2*m)) :
    (support_graph (not_set_coloring_ramsey_property_p3_one_even_threshold_rrPhi a b m hb hm hbm) {c}).Adj v x ↔
      (not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m v x).val = c.val / b ∧ v ≠ x := by
  rw [support_graph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨hh, hsub⟩, hne⟩
    have hc : c ∈ not_set_coloring_ramsey_property_p3_one_even_threshold_rrPhi a b m hb hm hbm ⟨s(v,x), hh⟩ :=
      Finset.singleton_subset_iff.mp hsub
    have hc' : c ∈ not_set_coloring_ramsey_property_p3_one_even_threshold_rrG a b m hb hm hbm s(v,x) := hc
    rw [not_set_coloring_ramsey_property_p3_one_even_threshold_rrG_mem, Sym2.lift_mk] at hc'
    exact ⟨hc', hne⟩
  · rintro ⟨hval, hne⟩
    have hmem_top : s(v,x) ∈ (⊤ : SimpleGraph (Fin (2*m))).edgeSet := by
      rw [SimpleGraph.edgeSet_top]
      simp [Sym2.mk_isDiag_iff, hne]
    refine ⟨⟨hmem_top, ?_⟩, hne⟩
    rw [Finset.singleton_subset_iff]
    show c ∈ not_set_coloring_ramsey_property_p3_one_even_threshold_rrG a b m hb hm hbm s(v,x)
    rw [not_set_coloring_ramsey_property_p3_one_even_threshold_rrG_mem, Sym2.lift_mk]
    exact hval

private lemma not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx_val_eq_imp_eq (m : ℕ) (hm : 1 ≤ m)
    {v x y : Fin (2*m)} (hvx : v ≠ x) (hvy : v ≠ y)
    (hE : not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m v x =
      not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m v y) : x = y := by
  haveI : NeZero (2*m-1) := ⟨by omega⟩
  have key2 : (2 : ZMod (2*m-1)) * (m : ZMod (2*m-1)) = 1 := by
    have hh : (2*m - 1) + 1 = 2*m := by omega
    have h : ((2*m : ℕ) : ZMod (2*m-1)) = 1 := by
      rw [← hh, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    rwa [Nat.cast_mul, Nat.cast_ofNat] at h
  have cancel : ∀ p q : ZMod (2*m-1), p * (m : ZMod (2*m-1)) = q * (m : ZMod (2*m-1)) → p = q := by
    intro p q h
    calc p = p * ((2:ZMod (2*m-1)) * m) := by rw [key2, mul_one]
      _ = (p * m) * 2 := by ring
      _ = (q * m) * 2 := by rw [h]
      _ = q * ((2:ZMod (2*m-1)) * m) := by ring
      _ = q := by rw [key2, mul_one]
  by_cases hv : v.val = 2*m-1
  · have hxS : x.val ≠ 2*m-1 := by intro h; exact hvx (Fin.ext (by rw [hv, h]))
    have hyS : y.val ≠ 2*m-1 := by intro h; exact hvy (Fin.ext (by rw [hv, h]))
    have hxy : ((x.val : ℕ) : ZMod (2*m-1)) = ((y.val : ℕ) : ZMod (2*m-1)) := by
      simpa [not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx, hv, hxS, hyS] using hE
    exact Fin.ext (not_set_coloring_ramsey_property_p3_one_even_threshold_zmod_natcast_eq_of_lt
      (by have := x.isLt; omega) (by have := y.isLt; omega) hxy)
  · by_cases hxS : x.val = 2*m-1
    · by_cases hyS : y.val = 2*m-1
      · exact Fin.ext (by rw [hxS, hyS])
      · have hEq : ((v.val : ℕ) : ZMod (2*m-1)) =
            (((v.val : ℕ) : ZMod (2*m-1)) + ((y.val : ℕ) : ZMod (2*m-1))) * (m : ZMod (2*m-1)) := by
          simpa [not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx, hv, hxS, hyS] using hE
        have hstep : (2:ZMod (2*m-1)) * ((((v.val : ℕ) : ZMod (2*m-1)) + ((y.val : ℕ) : ZMod (2*m-1))) * (m : ZMod (2*m-1)))
            = ((v.val : ℕ) : ZMod (2*m-1)) + ((y.val : ℕ) : ZMod (2*m-1)) := by
          rw [show (2:ZMod (2*m-1)) * ((((v.val : ℕ) : ZMod (2*m-1)) + ((y.val : ℕ) : ZMod (2*m-1))) * (m : ZMod (2*m-1)))
              = (((v.val : ℕ) : ZMod (2*m-1)) + ((y.val : ℕ) : ZMod (2*m-1))) * ((2:ZMod (2*m-1)) * (m : ZMod (2*m-1))) by ring, key2, mul_one]
        have hmul : (2:ZMod (2*m-1)) * ((v.val : ℕ) : ZMod (2*m-1)) =
            ((v.val : ℕ) : ZMod (2*m-1)) + ((y.val : ℕ) : ZMod (2*m-1)) := by
          rw [← hstep]; exact congrArg (fun z => (2:ZMod (2*m-1)) * z) hEq
        have hvy' : ((v.val : ℕ) : ZMod (2*m-1)) = ((y.val : ℕ) : ZMod (2*m-1)) := by
          linear_combination hmul
        have hve : v.val < 2*m-1 := by have := v.isLt; omega
        have hye : y.val < 2*m-1 := by have := y.isLt; omega
        exact absurd (Fin.ext (not_set_coloring_ramsey_property_p3_one_even_threshold_zmod_natcast_eq_of_lt hve hye hvy')) hvy
    · by_cases hyS : y.val = 2*m-1
      · have hEq : ((v.val : ℕ) : ZMod (2*m-1)) =
            (((v.val : ℕ) : ZMod (2*m-1)) + ((x.val : ℕ) : ZMod (2*m-1))) * (m : ZMod (2*m-1)) := by
          simpa [not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx, hv, hxS, hyS] using hE.symm
        have hstep : (2:ZMod (2*m-1)) * ((((v.val : ℕ) : ZMod (2*m-1)) + ((x.val : ℕ) : ZMod (2*m-1))) * (m : ZMod (2*m-1)))
            = ((v.val : ℕ) : ZMod (2*m-1)) + ((x.val : ℕ) : ZMod (2*m-1)) := by
          rw [show (2:ZMod (2*m-1)) * ((((v.val : ℕ) : ZMod (2*m-1)) + ((x.val : ℕ) : ZMod (2*m-1))) * (m : ZMod (2*m-1)))
              = (((v.val : ℕ) : ZMod (2*m-1)) + ((x.val : ℕ) : ZMod (2*m-1))) * ((2:ZMod (2*m-1)) * (m : ZMod (2*m-1))) by ring, key2, mul_one]
        have hmul : (2:ZMod (2*m-1)) * ((v.val : ℕ) : ZMod (2*m-1)) =
            ((v.val : ℕ) : ZMod (2*m-1)) + ((x.val : ℕ) : ZMod (2*m-1)) := by
          rw [← hstep]; exact congrArg (fun z => (2:ZMod (2*m-1)) * z) hEq
        have hvx' : ((v.val : ℕ) : ZMod (2*m-1)) = ((x.val : ℕ) : ZMod (2*m-1)) := by
          linear_combination hmul
        have hve : v.val < 2*m-1 := by have := v.isLt; omega
        have hxe : x.val < 2*m-1 := by have := x.isLt; omega
        exact absurd (Fin.ext (not_set_coloring_ramsey_property_p3_one_even_threshold_zmod_natcast_eq_of_lt hve hxe hvx')) hvx
      · have hEq : ((((v.val : ℕ) : ZMod (2*m-1)) + ((x.val : ℕ) : ZMod (2*m-1))) * (m : ZMod (2*m-1)))
            = (((v.val : ℕ) : ZMod (2*m-1)) + ((y.val : ℕ) : ZMod (2*m-1))) * (m : ZMod (2*m-1)) := by
          simpa [not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx, hv, hxS, hyS] using hE
        have hcancel := cancel _ _ hEq
        have hxy : ((x.val : ℕ) : ZMod (2*m-1)) = ((y.val : ℕ) : ZMod (2*m-1)) := add_left_cancel hcancel
        exact Fin.ext (not_set_coloring_ramsey_property_p3_one_even_threshold_zmod_natcast_eq_of_lt
          (by have := x.isLt; omega) (by have := y.isLt; omega) hxy)

private lemma not_set_coloring_ramsey_property_p3_one_even_threshold_rr_support_adj_unique (a b m : ℕ) (hb : 1 ≤ b) (hm : 1 ≤ m)
    (hbm : b * (2*m - 1) ≤ a) (c : Fin a) :
    ∀ v x y, (support_graph (not_set_coloring_ramsey_property_p3_one_even_threshold_rrPhi a b m hb hm hbm) {c}).Adj v x →
      (support_graph (not_set_coloring_ramsey_property_p3_one_even_threshold_rrPhi a b m hb hm hbm) {c}).Adj v y → x = y := by
  intro v x y hx hy
  rw [not_set_coloring_ramsey_property_p3_one_even_threshold_rr_adj] at hx hy
  obtain ⟨hvx, hnex⟩ := hx
  obtain ⟨hvy, hney⟩ := hy
  haveI : NeZero (2*m-1) := ⟨by omega⟩
  have hEq : not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m v x =
      not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx m v y :=
    ZMod.val_injective _ (by rw [hvx, hvy])
  exact not_set_coloring_ramsey_property_p3_one_even_threshold_rrIdx_val_eq_imp_eq m hm hnex hney hEq

private lemma not_set_coloring_ramsey_property_p3_one_even_threshold_rr_no_p3 (a b m : ℕ) (hb : 1 ≤ b) (hm : 1 ≤ m)
    (hbm : b * (2*m - 1) ≤ a) (c : Fin a) :
    ¬ (SimpleGraph.pathGraph 3).IsContained
      (support_graph (not_set_coloring_ramsey_property_p3_one_even_threshold_rrPhi a b m hb hm hbm) {c}) :=
  not_set_coloring_ramsey_property_p3_one_even_threshold_no_p3_of_adj_unique
    (not_set_coloring_ramsey_property_p3_one_even_threshold_rr_support_adj_unique a b m hb hm hbm c)

private lemma not_set_coloring_ramsey_property_p3_one_even_threshold_rr_phi_card (a b m : ℕ) (hb : 1 ≤ b) (hm : 1 ≤ m)
    (hbm : b * (2*m - 1) ≤ a) (e : (⊤ : SimpleGraph (Fin (2*m))).edgeSet) :
    (not_set_coloring_ramsey_property_p3_one_even_threshold_rrPhi a b m hb hm hbm e).card = b :=
  not_set_coloring_ramsey_property_p3_one_even_threshold_rrG_card a b m hb hm hbm (e : Sym2 (Fin (2*m)))

private lemma not_set_coloring_ramsey_property_p3_one_even_threshold_exists_coloring_even (a b m : ℕ) (hb : 1 ≤ b) (hm : 1 ≤ m)
    (hbm : b * (2*m - 1) ≤ a) :
    ¬ set_coloring_ramsey_property (SimpleGraph.pathGraph 3) a b 1 (2*m) := by
  intro hprop
  rw [set_coloring_ramsey_property] at hprop
  obtain ⟨T, hTcard, hTcontain⟩ := hprop
    (not_set_coloring_ramsey_property_p3_one_even_threshold_rrPhi a b m hb hm hbm)
    (not_set_coloring_ramsey_property_p3_one_even_threshold_rr_phi_card a b m hb hm hbm)
  obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hTcard
  exact not_set_coloring_ramsey_property_p3_one_even_threshold_rr_no_p3 a b m hb hm hbm c hTcontain

/-- The complete graph on 2 * ⌊(a+b)/(2b)⌋ vertices admits an (a,b)-set-coloring avoiding monochromatic P_3. -/
theorem not_set_coloring_ramsey_property_p3_one_even_threshold (a b : ℕ) (hba : b ≤ a) (hb : 1 ≤ b) :
    ¬ set_coloring_ramsey_property (SimpleGraph.pathGraph 3) a b 1 (2 * ((a + b) / (2 * b))) := by
  set m := (a + b) / (2 * b) with hm_def
  have hb2 : 0 < 2 * b := by omega
  have hm : 1 ≤ m := by
    rw [hm_def, Nat.le_div_iff_mul_le hb2]; omega
  have hle : 2 * b * m ≤ a + b := by
    rw [hm_def]
    have := Nat.div_mul_le_self (a + b) (2 * b)
    calc 2 * b * ((a + b) / (2 * b)) = (a + b) / (2 * b) * (2 * b) := by ring
      _ ≤ a + b := this
  have hbm : b * (2*m - 1) ≤ a := by
    have hstep : b * (2*m - 1) + b = 2*b*m := by
      rw [show b * (2*m-1) + b = b * ((2*m-1)+1) by rw [Nat.mul_succ]]
      have hh : (2*m-1)+1 = 2*m := by omega
      rw [hh]; ring
    omega
  exact not_set_coloring_ramsey_property_p3_one_even_threshold_exists_coloring_even a b m hb hm hbm
