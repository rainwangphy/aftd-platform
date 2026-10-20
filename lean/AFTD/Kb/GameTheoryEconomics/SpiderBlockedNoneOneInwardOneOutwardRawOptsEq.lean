import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderRhoZeroSame
import AFTD.Kb.GameTheoryEconomics.SpiderNoneOneInwardOneOutwardRawOpts
import AFTD.Kb.GameTheoryEconomics.SpiderUpdateCentre
import AFTD.Kb.GameTheoryEconomics.SpiderGammaRotateThreeShortLegs
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderRhoStar
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.NatMexList

/-!
# spider_blocked_none_one_inward_one_outward_raw_opts_eq

Topic: combinatorial_games   Node: 91508c9f93a6

Provenance: helper lemma. step towards spider_blocked_none_one_inward_one_outward

For r ≥ 2 and φ ≠ free, the value of (none;{(1,inward),(1,outward),(r,φ)}) at fuel r+3 is the mex of the raw option list spider_none_one_inward_one_outward_raw_opts r φ.
-/

lemma spider_blocked_none_one_inward_one_outward_raw_opts_eq_range_succ_two (n : ℕ) :
    List.range (n + 2) = 0 :: (List.map (· + 1) (List.range n) ++ [n + 1]) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, List.range_succ, ih]
    rw [show k + 1 + 1 = k + 2 by ring]
    rw [List.range_succ (n := k), List.map_append]
    simp [List.cons_append, List.append_assoc]

lemma spider_blocked_none_one_inward_one_outward_raw_opts_eq_range_split (r : ℕ) (hr : 2 ≤ r) :
    List.range r = 0 :: (List.map (· + 1) (List.range (r - 2)) ++ [r - 1]) := by
  conv => lhs; rw [show r = (r - 2) + 2 by omega]
  rw [spider_blocked_none_one_inward_one_outward_raw_opts_eq_range_succ_two]
  rw [show r - 2 + 1 = r - 1 by omega]

lemma spider_blocked_none_one_inward_one_outward_raw_opts_eq_opt_leg0 (r : ℕ) (φ : SpiderLegEnd) :
    (List.filterMap
        (fun delta =>
          if (0 + 1 == 1) = true ∧ SpiderLegEnd.inward ≠ SpiderLegEnd.free ∧ delta ≠ SpiderLegEnd.inward then none
          else
            if 0 + 1 ≥ 2 then
              some
                (spider_rho (1 - (0 + 1)) delta SpiderLegEnd.inward ^^^
                  spider_gamma (r + 2) CentreStatus.none
                    ((0 + 1 - 1, delta) :: [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r, φ)].eraseIdx 0))
            else
              some
                (spider_rho (1 - (0 + 1)) delta SpiderLegEnd.inward ^^^
                  spider_gamma (r + 2) (spider_update_centre CentreStatus.none delta)
                    ([(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r, φ)].eraseIdx 0)))
        [SpiderLegEnd.inward, SpiderLegEnd.outward]) =
    [spider_gamma (r + 2) CentreStatus.incoming [(1, SpiderLegEnd.outward), (r, φ)]] := by
  simp [spider_rho, spider_update_centre]

lemma spider_blocked_none_one_inward_one_outward_raw_opts_eq_opt_leg1 (r : ℕ) (φ : SpiderLegEnd) :
    (List.filterMap
        (fun delta =>
          if (0 + 1 == 1) = true ∧ SpiderLegEnd.outward ≠ SpiderLegEnd.free ∧ delta ≠ SpiderLegEnd.outward then none
          else
            if 0 + 1 ≥ 2 then
              some
                (spider_rho (1 - (0 + 1)) delta SpiderLegEnd.outward ^^^
                  spider_gamma (r + 2) CentreStatus.none
                    ((0 + 1 - 1, delta) :: [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r, φ)].eraseIdx 1))
            else
              some
                (spider_rho (1 - (0 + 1)) delta SpiderLegEnd.outward ^^^
                  spider_gamma (r + 2) (spider_update_centre CentreStatus.none delta)
                    ([(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r, φ)].eraseIdx 1)))
        [SpiderLegEnd.inward, SpiderLegEnd.outward]) =
    [spider_gamma (r + 2) CentreStatus.outgoing [(1, SpiderLegEnd.inward), (r, φ)]] := by
  simp [spider_rho, spider_update_centre]

lemma spider_blocked_none_one_inward_one_outward_raw_opts_eq_opt_leg2_zero (r : ℕ) (hr : 2 ≤ r) (φ : SpiderLegEnd) :
    (List.filterMap
        (fun delta =>
          if (0 + 1 == r) = true ∧ φ ≠ SpiderLegEnd.free ∧ delta ≠ φ then none
          else
            if 0 + 1 ≥ 2 then
              some
                (spider_rho (r - (0 + 1)) delta φ ^^^
                  spider_gamma (r + 2) CentreStatus.none
                    ((0 + 1 - 1, delta) ::
                      [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r, φ)].eraseIdx 2))
            else
              some
                (spider_rho (r - (0 + 1)) delta φ ^^^
                  spider_gamma (r + 2) (spider_update_centre CentreStatus.none delta)
                    ([(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r, φ)].eraseIdx 2)))
        [SpiderLegEnd.inward, SpiderLegEnd.outward]) =
    [spider_rho (r - 1) SpiderLegEnd.inward φ ^^^
        spider_gamma (r + 2) CentreStatus.incoming [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward)],
      spider_rho (r - 1) SpiderLegEnd.outward φ ^^^
        spider_gamma (r + 2) CentreStatus.outgoing [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward)]] := by
  have : (0 + 1 == r) = false := beq_false_of_ne (by omega)
  simp [this, spider_update_centre]

lemma spider_blocked_none_one_inward_one_outward_raw_opts_eq_opt_leg2_mid (r : ℕ) (hr : 2 ≤ r) (φ : SpiderLegEnd)
    (a : ℕ) (ha : a ∈ List.range (r - 2)) :
    (List.filterMap
        (fun delta =>
          if (a + 1 + 1 == r) = true ∧ φ ≠ SpiderLegEnd.free ∧ delta ≠ φ then none
          else
            if a + 1 + 1 ≥ 2 then
              some
                (spider_rho (r - (a + 1 + 1)) delta φ ^^^
                  spider_gamma (r + 2) CentreStatus.none
                    ((a + 1 + 1 - 1, delta) ::
                      [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r, φ)].eraseIdx 2))
            else
              some
                (spider_rho (r - (a + 1 + 1)) delta φ ^^^
                  spider_gamma (r + 2) (spider_update_centre CentreStatus.none delta)
                    ([(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r, φ)].eraseIdx 2)))
        [SpiderLegEnd.inward, SpiderLegEnd.outward]) =
    [spider_rho (r - 2 - a) SpiderLegEnd.inward φ ^^^
        spider_gamma (r + 2) CentreStatus.none
          [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (a + 1, SpiderLegEnd.inward)],
      spider_rho (r - 2 - a) SpiderLegEnd.outward φ ^^^
        spider_gamma (r + 2) CentreStatus.none
          [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (a + 1, SpiderLegEnd.outward)]] := by
  have hlt : a < r - 2 := List.mem_range.mp ha
  have hne : (a + 1 + 1 == r) = false := beq_false_of_ne (by omega)
  have hge : 2 ≤ a + 1 + 1 := by omega
  have harith1 : r - (a + 1 + 1) = r - 2 - a := by omega
  have harith2 : a + 1 + 1 - 1 = a + 1 := by omega
  simp [hne, hge, harith1, harith2, spider_gamma_rotate_three_short_legs]

lemma spider_blocked_none_one_inward_one_outward_raw_opts_eq_opt_leg2_last (r : ℕ) (hr : 2 ≤ r) (φ : SpiderLegEnd)
    (hφ : φ ≠ SpiderLegEnd.free) :
    (List.filterMap
        (fun delta =>
          if (r - 1 + 1 == r) = true ∧ φ ≠ SpiderLegEnd.free ∧ delta ≠ φ then none
          else
            if r - 1 + 1 ≥ 2 then
              some
                (spider_rho (r - (r - 1 + 1)) delta φ ^^^
                  spider_gamma (r + 2) CentreStatus.none
                    ((r - 1 + 1 - 1, delta) ::
                      [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r, φ)].eraseIdx 2))
            else
              some
                (spider_rho (r - (r - 1 + 1)) delta φ ^^^
                  spider_gamma (r + 2) (spider_update_centre CentreStatus.none delta)
                    ([(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r, φ)].eraseIdx 2)))
        [SpiderLegEnd.inward, SpiderLegEnd.outward]) =
    [spider_rho 0 φ φ ^^^
        spider_gamma (r + 2) CentreStatus.none [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r - 1, φ)]] := by
  have heq : (r - 1 + 1 == r) = true := by rw [beq_iff_eq]; omega
  have hge : 2 ≤ r - 1 + 1 := by omega
  have hsub1 : r - (r - 1 + 1) = 0 := by omega
  have hsub2 : r - 1 + 1 - 1 = r - 1 := by omega
  cases φ with
  | free => contradiction
  | inward => simp [heq, hge, hsub1, hsub2, spider_gamma_rotate_three_short_legs]
  | outward => simp [heq, hge, hsub1, hsub2, spider_gamma_rotate_three_short_legs]

/-- One definitional unfolding step of the κ₁ root state, giving the raw option list. -/
theorem spider_blocked_none_one_inward_one_outward_raw_opts_eq (r : ℕ) (hr : 2 ≤ r) (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    spider_gamma (r + 3) CentreStatus.none [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), (r, φ)] =
      nat_mex_list (spider_none_one_inward_one_outward_raw_opts r φ) := by
  rw [spider_gamma.eq_def]
  dsimp only
  apply congr_arg nat_mex_list
  change
    List.flatMap _ [((1, SpiderLegEnd.inward), 0), ((1, SpiderLegEnd.outward), 1), ((r, φ), 2)] = _
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil]
  dsimp only
  have hr1 : List.range 1 = [0] := rfl
  rw [hr1]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [spider_blocked_none_one_inward_one_outward_raw_opts_eq_range_split r hr]
  rw [List.flatMap_cons, List.flatMap_append, List.flatMap_map, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  unfold spider_none_one_inward_one_outward_raw_opts
  rw [spider_blocked_none_one_inward_one_outward_raw_opts_eq_opt_leg0]
  rw [spider_blocked_none_one_inward_one_outward_raw_opts_eq_opt_leg1]
  rw [spider_blocked_none_one_inward_one_outward_raw_opts_eq_opt_leg2_zero r hr]
  rw [List.flatMap_congr (spider_blocked_none_one_inward_one_outward_raw_opts_eq_opt_leg2_mid r hr φ)]
  rw [spider_blocked_none_one_inward_one_outward_raw_opts_eq_opt_leg2_last r hr φ hφ]
  simp [List.cons_append]
