import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.SpiderUpdateCentre
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderRhoStar

/-!
# spider_gamma_fuel_independent

Topic: combinatorial_games   Node: 8cca7ed89c7c

Provenance: helper lemma. step towards spider_eventual_parity_two_three

For every fuel at least the total number of markable edges in L plus one, the value of spider_gamma does not depend on the fuel: it equals the value at the canonical fuel (sum of leg lengths) + 1.
-/

lemma spider_gamma_fuel_independent_sum_eraseIdx_eq (L : List (ℕ × SpiderLegEnd)) (idx : ℕ) (h_idx : idx < L.length) :
    ((L.eraseIdx idx).map Prod.fst).sum + (L[idx].1) = (L.map Prod.fst).sum := by
  have hlen : idx < (L.map Prod.fst).length := by simpa using h_idx
  have hp := (L.map Prod.fst).getElem_cons_eraseIdx_perm hlen
  have hsum := hp.sum_eq
  rw [← List.eraseIdx_map]
  simp only [List.sum_cons, List.getElem_map] at hsum
  omega

lemma spider_gamma_fuel_independent_sum_branch1_lt (L : List (ℕ × SpiderLegEnd)) (idx : ℕ) (h_idx : idx < L.length)
    (h : ℕ) (hh : L[idx].1 = h) (j_zero : ℕ) (hj : j_zero < h) :
    ((L.eraseIdx idx).map Prod.fst).sum < (L.map Prod.fst).sum := by
  have := spider_gamma_fuel_independent_sum_eraseIdx_eq L idx h_idx
  rw [hh] at this
  omega

lemma spider_gamma_fuel_independent_sum_branch2_lt (L : List (ℕ × SpiderLegEnd)) (idx : ℕ) (h_idx : idx < L.length)
    (h : ℕ) (hh : L[idx].1 = h) (j_zero : ℕ) (hj : j_zero < h)
    (delta : SpiderLegEnd) :
    (((j_zero + 1 - 1, delta) :: (L.eraseIdx idx)).map Prod.fst).sum < (L.map Prod.fst).sum := by
  have := spider_gamma_fuel_independent_sum_eraseIdx_eq L idx h_idx
  rw [hh] at this
  simp only [List.map_cons, List.sum_cons]
  omega

lemma spider_gamma_fuel_independent_aux (n : ℕ) :
    ∀ (L : List (ℕ × SpiderLegEnd)) (_ : (L.map Prod.fst).sum = n)
      (fuel1 fuel2 : ℕ) (s : CentreStatus)
      (_h1 : (L.map Prod.fst).sum + 1 ≤ fuel1) (_h2 : (L.map Prod.fst).sum + 1 ≤ fuel2),
      spider_gamma fuel1 s L = spider_gamma fuel2 s L := by
  induction' n using Nat.strong_induction_on with n IH
  intro L hn fuel1 fuel2 s _h1 _h2
  cases fuel1 with
  | zero => omega
  | succ f1 =>
    cases fuel2 with
    | zero => omega
    | succ f2 =>
      by_cases hs : s = CentreStatus.free
      · subst hs; rw [spider_gamma.eq_def, spider_gamma.eq_def]
      · match L with
        | [] => rw [spider_gamma.eq_def, spider_gamma.eq_def]
        | [(h, phi)] => rw [spider_gamma.eq_def, spider_gamma.eq_def]
        | a :: b :: rest =>
          have hL1 : (a :: b :: rest) ≠ [] := by simp
          have hL2 : ∀ h phi, (a :: b :: rest) ≠ [(h, phi)] := by intro h phi; simp
          rw [spider_gamma.eq_7 s (a :: b :: rest) f1 hs hL1 hL2]
          rw [spider_gamma.eq_7 s (a :: b :: rest) f2 hs hL1 hL2]
          congr 1
          apply List.flatMap_congr
          intro ⟨⟨h, phi⟩, idx⟩ h_mem
          have h_zip := List.mem_zipIdx h_mem
          have h_idx : idx < (a :: b :: rest).length := by simpa using h_zip.2.1
          have h_eq : (h, phi) = (a :: b :: rest)[idx] := by simpa using h_zip.2.2
          have hh : (a :: b :: rest)[idx].1 = h := by rw [← h_eq]
          apply List.flatMap_congr
          intro j_zero hj_mem
          have hj : j_zero < h := List.mem_range.mp hj_mem
          apply List.filterMap_congr
          intro delta hdelta_mem
          split_ifs with h1_cond h2_cond
          · rfl
          · dsimp only
            have h_lt := spider_gamma_fuel_independent_sum_branch2_lt (a :: b :: rest) idx h_idx h hh j_zero hj delta
            rw [hn] at h_lt
            have h_IH := IH _ h_lt ((j_zero + 1 - 1, delta) :: (a :: b :: rest).eraseIdx idx) rfl f1 f2 s (by omega) (by omega)
            rw [h_IH]
          · dsimp only
            have h_lt := spider_gamma_fuel_independent_sum_branch1_lt (a :: b :: rest) idx h_idx h hh j_zero hj
            rw [hn] at h_lt
            have h_IH := IH _ h_lt ((a :: b :: rest).eraseIdx idx) rfl f1 f2 (spider_update_centre s delta) (by omega) (by omega)
            rw [h_IH]

/-- spider_gamma is independent of the fuel once the fuel is at least the total leg length plus one. -/
theorem spider_gamma_fuel_independent (fuel : ℕ) (s : CentreStatus) (L : List (ℕ × SpiderLegEnd))
    (hfuel : (L.map Prod.fst).sum + 1 ≤ fuel) :
    spider_gamma fuel s L = spider_gamma ((L.map Prod.fst).sum + 1) s L := by
  exact spider_gamma_fuel_independent_aux (L.map Prod.fst).sum L rfl fuel ((L.map Prod.fst).sum + 1) s hfuel (by omega)
