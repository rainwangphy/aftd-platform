import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderReverseLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderReverseCentreStatus
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.SpiderUpdateCentre
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderRhoStar

/-!
# spider_gamma_reversal

Topic: combinatorial_games   Node: f909d1896619

Provenance: helper lemma. step towards spider_eventual_parity_two_three

For every fuel, centre status s and leg list L, the value of the spider state (s;L) equals the value of the state obtained by exchanging incoming and outgoing in the centre status and in every far end of L.
-/

lemma spider_gamma_reversal_rho_star (h : ℕ) (phi : SpiderLegEnd) :
    spider_rho_star h (spider_reverse_leg_end phi) = spider_rho_star h phi := by
  cases phi <;> rfl

lemma spider_gamma_reversal_free_foldl (L : List (ℕ × SpiderLegEnd)) (acc : ℕ) :
    List.foldl (fun acc p => acc ^^^ spider_rho_star p.1 (spider_reverse_leg_end p.2)) acc L =
      List.foldl (fun acc p => acc ^^^ spider_rho_star p.1 p.2) acc L := by
  induction L generalizing acc with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldl_cons, List.foldl_cons, spider_gamma_reversal_rho_star]
    exact ih _

lemma spider_gamma_reversal_leg_end_inj (a b : SpiderLegEnd) :
    spider_reverse_leg_end a = spider_reverse_leg_end b ↔ a = b := by
  constructor
  · intro h; cases a <;> cases b <;> revert h <;> decide
  · intro h; rw [h]

lemma spider_gamma_reversal_leg_end_ne (a b : SpiderLegEnd) :
    spider_reverse_leg_end a ≠ spider_reverse_leg_end b ↔ a ≠ b := by
  rw [not_iff_not, spider_gamma_reversal_leg_end_inj]

lemma spider_gamma_reversal_leg_end_ne_free (x : SpiderLegEnd) :
    spider_reverse_leg_end x ≠ SpiderLegEnd.free ↔ x ≠ SpiderLegEnd.free := by
  cases x <;> simp [spider_reverse_leg_end]

lemma spider_gamma_reversal_rho (h : ℕ) (delta phi : SpiderLegEnd) :
    spider_rho h (spider_reverse_leg_end delta) (spider_reverse_leg_end phi) = spider_rho h delta phi := by
  cases delta <;> cases phi <;> rfl

lemma spider_gamma_reversal_update_centre (s : CentreStatus) (delta : SpiderLegEnd) :
    spider_update_centre (spider_reverse_centre_status s) (spider_reverse_leg_end delta) =
      spider_reverse_centre_status (spider_update_centre s delta) := by
  cases s <;> cases delta <;> rfl

theorem spider_gamma_reversal_filterMap_option_eq
    (fuel : ℕ)
    (ih : ∀ (s : CentreStatus) (L : List (ℕ × SpiderLegEnd)),
      spider_gamma fuel s L = spider_gamma fuel (spider_reverse_centre_status s)
        (L.map (fun p => (p.1, spider_reverse_leg_end p.2))))
    (s : CentreStatus) (rest : List (ℕ × SpiderLegEnd))
    (h j : ℕ) (phi delta : SpiderLegEnd) :
    (if (j == h) = true ∧ spider_reverse_leg_end phi ≠ SpiderLegEnd.free ∧ spider_reverse_leg_end delta ≠ spider_reverse_leg_end phi then Option.none
     else
       have d := spider_rho (h - j) (spider_reverse_leg_end delta) (spider_reverse_leg_end phi);
       if j ≥ 2 then
         have new_L := (j - 1, spider_reverse_leg_end delta) :: rest.map (fun p => (p.1, spider_reverse_leg_end p.2));
         some (d ^^^ spider_gamma fuel (spider_reverse_centre_status s) new_L)
       else
         have new_s := spider_update_centre (spider_reverse_centre_status s) (spider_reverse_leg_end delta);
         some (d ^^^ spider_gamma fuel new_s (rest.map (fun p => (p.1, spider_reverse_leg_end p.2)))))
    =
    (if (j == h) = true ∧ phi ≠ SpiderLegEnd.free ∧ delta ≠ phi then Option.none
     else
       have d := spider_rho (h - j) delta phi;
       if j ≥ 2 then
         have new_L := (j - 1, delta) :: rest;
         some (d ^^^ spider_gamma fuel s new_L)
       else
         have new_s := spider_update_centre s delta;
         some (d ^^^ spider_gamma fuel new_s rest)) := by
  simp only [spider_gamma_reversal_leg_end_ne_free, spider_gamma_reversal_leg_end_ne, spider_gamma_reversal_rho]
  split_ifs with hc hj
  · rfl
  · rw [ih s ((j - 1, delta) :: rest)]
    rfl
  · rw [spider_gamma_reversal_update_centre]
    rw [ih (spider_update_centre s delta) rest]

lemma spider_gamma_reversal_filterMap_two_perm (F G : SpiderLegEnd → Option ℕ)
    (h_rev : ∀ delta, G (spider_reverse_leg_end delta) = F delta) :
    ([SpiderLegEnd.inward, SpiderLegEnd.outward].filterMap G).Perm
      ([SpiderLegEnd.inward, SpiderLegEnd.outward].filterMap F) := by
  have h1 : [SpiderLegEnd.inward, SpiderLegEnd.outward].filterMap G =
      ([SpiderLegEnd.outward, SpiderLegEnd.inward].map spider_reverse_leg_end).filterMap G := by rfl
  rw [h1, List.filterMap_map]
  have hcomp : (G ∘ spider_reverse_leg_end) = F := by
    funext d; exact h_rev d
  rw [hcomp]
  have h2 : [SpiderLegEnd.outward, SpiderLegEnd.inward] = [SpiderLegEnd.inward, SpiderLegEnd.outward].reverse := rfl
  rw [h2, List.filterMap_reverse]
  exact List.reverse_perm _

def spider_gamma_reversal_options (fuel : ℕ) (s : CentreStatus) (L : List (ℕ × SpiderLegEnd)) : List ℕ :=
  List.flatMap
    (fun x =>
      match x with
      | ((h, phi), idx) =>
        have rest := L.eraseIdx idx;
        List.flatMap
          (fun j_zero =>
            have j := j_zero + 1;
            List.filterMap
              (fun delta =>
                if (j == h) = true ∧ phi ≠ SpiderLegEnd.free ∧ delta ≠ phi then Option.none
                else
                  have d := spider_rho (h - j) delta phi;
                  if j ≥ 2 then
                    have new_L := (j - 1, delta) :: rest;
                    some (d ^^^ spider_gamma fuel s new_L)
                  else
                    have new_s := spider_update_centre s delta;
                    some (d ^^^ spider_gamma fuel new_s rest))
              [SpiderLegEnd.inward, SpiderLegEnd.outward])
          (List.range h))
    L.zipIdx

lemma spider_gamma_reversal_options_perm (fuel : ℕ)
    (ih : ∀ (s : CentreStatus) (L : List (ℕ × SpiderLegEnd)),
      spider_gamma fuel s L = spider_gamma fuel (spider_reverse_centre_status s)
        (L.map (fun p => (p.1, spider_reverse_leg_end p.2))))
    (s : CentreStatus) (L : List (ℕ × SpiderLegEnd)) :
    (spider_gamma_reversal_options fuel (spider_reverse_centre_status s)
      (L.map (fun p => (p.1, spider_reverse_leg_end p.2)))).Perm
    (spider_gamma_reversal_options fuel s L) := by
  unfold spider_gamma_reversal_options
  have hzip : (L.map (fun p => (p.1, spider_reverse_leg_end p.2))).zipIdx =
      L.zipIdx.map (fun ((h, phi), idx) => ((h, spider_reverse_leg_end phi), idx)) := by
    rw [List.zipIdx_map]
    rfl
  rw [hzip, List.flatMap_map]
  apply List.Perm.flatMap_left
  intro ⟨⟨h, phi⟩, idx⟩ hmem
  dsimp only
  rw [List.eraseIdx_map]
  apply List.Perm.flatMap_left
  intro j_zero hjmem
  apply spider_gamma_reversal_filterMap_two_perm
  intro delta
  exact spider_gamma_reversal_filterMap_option_eq fuel ih s (L.eraseIdx idx) h (j_zero + 1) phi delta

lemma spider_gamma_reversal_nat_mex_list_loop_congr {l1 l2 : List ℕ} (hmem : ∀ x, x ∈ l1 ↔ x ∈ l2) (fuel : ℕ) (n : ℕ) :
    nat_mex_list.loop l1 n fuel = nat_mex_list.loop l2 n fuel := by
  induction fuel generalizing n with
  | zero =>
    rw [nat_mex_list.loop.eq_def, nat_mex_list.loop.eq_def]
  | succ fuel ih =>
    rw [nat_mex_list.loop.eq_def, nat_mex_list.loop.eq_def]
    by_cases hn : n ∈ l1
    · have hn2 : n ∈ l2 := (hmem n).mp hn
      simp [hn, hn2, ih]
    · have hn2 : n ∉ l2 := fun h => hn ((hmem n).mpr h)
      simp [hn, hn2]

lemma spider_gamma_reversal_nat_mex_list_eq_of_perm {l1 l2 : List ℕ} (h : l1.Perm l2) :
    nat_mex_list l1 = nat_mex_list l2 := by
  unfold nat_mex_list
  rw [h.length_eq]
  exact spider_gamma_reversal_nat_mex_list_loop_congr (fun _ => h.mem_iff) (l2.length + 1) 0

theorem spider_gamma_reversal_step (fuel : ℕ)
    (ih : ∀ (s : CentreStatus) (L : List (ℕ × SpiderLegEnd)),
      spider_gamma fuel s L = spider_gamma fuel (spider_reverse_centre_status s)
        (L.map (fun p => (p.1, spider_reverse_leg_end p.2))))
    (s : CentreStatus) (L : List (ℕ × SpiderLegEnd)) :
    spider_gamma (fuel + 1) s L =
      spider_gamma (fuel + 1) (spider_reverse_centre_status s)
        (L.map (fun p => (p.1, spider_reverse_leg_end p.2))) := by
  cases s
  · cases L with
    | nil => rw [spider_gamma.eq_def]; rw [spider_gamma.eq_def]; rfl
    | cons p1 tl =>
      cases tl with
      | nil =>
        rcases p1 with ⟨h, phi⟩
        rw [spider_gamma.eq_def]; rw [spider_gamma.eq_def]; rfl
      | cons p2 rest =>
        rw [spider_gamma.eq_def]; rw [spider_gamma.eq_def]
        dsimp only [spider_reverse_centre_status]
        exact (spider_gamma_reversal_nat_mex_list_eq_of_perm
          (spider_gamma_reversal_options_perm fuel ih CentreStatus.none (p1 :: p2 :: rest))).symm
  · cases L with
    | nil => rw [spider_gamma.eq_def]; rw [spider_gamma.eq_def]; rfl
    | cons p1 tl =>
      cases tl with
      | nil =>
        rcases p1 with ⟨h, phi⟩
        rw [spider_gamma.eq_def]; rw [spider_gamma.eq_def]
        dsimp only [spider_reverse_centre_status]
        have := (spider_gamma_reversal_rho h SpiderLegEnd.outward phi).symm
        exact this
      | cons p2 rest =>
        rw [spider_gamma.eq_def]; rw [spider_gamma.eq_def]
        dsimp only [spider_reverse_centre_status]
        exact (spider_gamma_reversal_nat_mex_list_eq_of_perm
          (spider_gamma_reversal_options_perm fuel ih CentreStatus.incoming (p1 :: p2 :: rest))).symm
  · cases L with
    | nil => rw [spider_gamma.eq_def]; rw [spider_gamma.eq_def]; rfl
    | cons p1 tl =>
      cases tl with
      | nil =>
        rcases p1 with ⟨h, phi⟩
        rw [spider_gamma.eq_def]; rw [spider_gamma.eq_def]
        dsimp only [spider_reverse_centre_status]
        have := (spider_gamma_reversal_rho h SpiderLegEnd.inward phi).symm
        exact this
      | cons p2 rest =>
        rw [spider_gamma.eq_def]; rw [spider_gamma.eq_def]
        dsimp only [spider_reverse_centre_status]
        exact (spider_gamma_reversal_nat_mex_list_eq_of_perm
          (spider_gamma_reversal_options_perm fuel ih CentreStatus.outgoing (p1 :: p2 :: rest))).symm
  · rw [spider_gamma.eq_def]; rw [spider_gamma.eq_def]
    dsimp [spider_reverse_centre_status]
    rw [List.foldl_map]
    exact (spider_gamma_reversal_free_foldl L 0).symm

/-- Reversing the centre status and every far end leaves the Grundy value unchanged (paper Lemma 8.3). -/
theorem spider_gamma_reversal (fuel : ℕ) (s : CentreStatus) (L : List (ℕ × SpiderLegEnd)) :
    spider_gamma fuel s L =
      spider_gamma fuel (spider_reverse_centre_status s)
        (L.map (fun p => (p.1, spider_reverse_leg_end p.2))) := by
  induction fuel generalizing s L with
  | zero =>
    rw [spider_gamma.eq_1, spider_gamma.eq_1]
  | succ fuel ih =>
    exact spider_gamma_reversal_step fuel ih s L
