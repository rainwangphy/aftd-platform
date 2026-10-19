import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderUpdateCentre
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderGamma

/-!
# spider_two_leg_one_free_options_eq

Topic: combinatorial_games   Node: e79ba2b54e58

Provenance: helper lemma. step towards spider_two_leg_one_free

The raw zipIdx.flatMap options list of [(1, free), (k, free)] at fuel k + 2 with incoming centre status unfolds to the explicit list [k, k % 2, (k - 1) ^^^ 1, (k - 1) ^^^ 1] concatenated with the flatMap over j ≥ 2 of (k - j) ^^^ spider_gamma (k + 1) incoming [(j - 1, delta), (1, free)].
-/

/-- Syntactic unfolding of the options list for [(1, free), (k, free)] at incoming centre status into head options and cuts of the long leg. -/
theorem spider_two_leg_one_free_options_eq (k : ℕ) (hk : 1 ≤ k) :
    ([(1, SpiderLegEnd.free), (k, SpiderLegEnd.free)].zipIdx.flatMap (fun ⟨⟨h, phi⟩, idx⟩ =>
      let rest := [(1, SpiderLegEnd.free), (k, SpiderLegEnd.free)].eraseIdx idx
      (List.range h).flatMap (fun j_zero =>
        let j := j_zero + 1
        [SpiderLegEnd.inward, SpiderLegEnd.outward].filterMap (fun delta =>
          if j == h ∧ phi ≠ SpiderLegEnd.free ∧ delta ≠ phi then none
          else
            let d := spider_rho (h - j) delta phi
            if j ≥ 2 then
              let new_L := (j - 1, delta) :: rest
              some (d ^^^ spider_gamma (k + 1) CentreStatus.incoming new_L)
            else
              let new_s := spider_update_centre CentreStatus.incoming delta
              some (d ^^^ spider_gamma (k + 1) new_s rest)
        )
      )
    )) =
    [k, k % 2, (k - 1) ^^^ 1, (k - 1) ^^^ 1] ++
    (List.range (k - 1)).flatMap (fun idx =>
      let j := idx + 2
      let d := k - j
      [SpiderLegEnd.inward, SpiderLegEnd.outward].map (fun delta =>
        d ^^^ spider_gamma (k + 1) CentreStatus.incoming [(idx + 1, delta), (1, SpiderLegEnd.free)]
      )
    ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have H0 : (let rest := [(m + 1, SpiderLegEnd.free)]
    (List.range 1).flatMap (fun j_zero =>
      let j := j_zero + 1
      [SpiderLegEnd.inward, SpiderLegEnd.outward].filterMap (fun delta =>
        if j == 1 ∧ SpiderLegEnd.free ≠ SpiderLegEnd.free ∧ delta ≠ SpiderLegEnd.free then none
        else
          let d := spider_rho (1 - j) delta SpiderLegEnd.free
          if j ≥ 2 then
            let new_L := (j - 1, delta) :: rest
            some (d ^^^ spider_gamma (m + 1 + 1) CentreStatus.incoming new_L)
          else
            let new_s := spider_update_centre CentreStatus.incoming delta
            some (d ^^^ spider_gamma (m + 1 + 1) new_s rest)
      ))) = [m + 1, (m + 1) % 2] := by
    change [0 ^^^ spider_gamma (m + 2) CentreStatus.incoming [(m + 1, SpiderLegEnd.free)],
            0 ^^^ spider_gamma (m + 2) CentreStatus.free [(m + 1, SpiderLegEnd.free)]] = [m + 1, (m + 1) % 2]
    have h1 : spider_gamma (m + 2) CentreStatus.incoming [(m + 1, SpiderLegEnd.free)] = m + 1 := rfl
    have h2 : spider_gamma (m + 2) CentreStatus.free [(m + 1, SpiderLegEnd.free)] = 0 ^^^ ((m + 1) % 2) := rfl
    simp [h1, h2]

  have H1_0 : (let rest := [(1, SpiderLegEnd.free)]
    let j_zero := 0
    let j := j_zero + 1
    [SpiderLegEnd.inward, SpiderLegEnd.outward].filterMap (fun delta =>
      if j == m + 1 ∧ SpiderLegEnd.free ≠ SpiderLegEnd.free ∧ delta ≠ SpiderLegEnd.free then none
      else
        let d := spider_rho (m + 1 - j) delta SpiderLegEnd.free
        if j ≥ 2 then
          let new_L := (j - 1, delta) :: rest
          some (d ^^^ spider_gamma (m + 1 + 1) CentreStatus.incoming new_L)
        else
          let new_s := spider_update_centre CentreStatus.incoming delta
          some (d ^^^ spider_gamma (m + 1 + 1) new_s rest)
    )) = [m ^^^ 1, m ^^^ 1] := by
    dsimp
    simp [List.filterMap_nil]
    have h1 : spider_gamma (m + 2) (spider_update_centre CentreStatus.incoming SpiderLegEnd.inward) [(1, SpiderLegEnd.free)] = 1 := rfl
    have h2 : spider_gamma (m + 2) (spider_update_centre CentreStatus.incoming SpiderLegEnd.outward) [(1, SpiderLegEnd.free)] = 1 := rfl
    have h3 : spider_rho m SpiderLegEnd.inward SpiderLegEnd.free = m := rfl
    have h4 : spider_rho m SpiderLegEnd.outward SpiderLegEnd.free = m := rfl
    rw [h1, h2, h3, h4]
    exact ⟨rfl, rfl⟩

  have H1_succ : ∀ idx, (let rest := [(1, SpiderLegEnd.free)]
    let j_zero := idx + 1
    let j := j_zero + 1
    [SpiderLegEnd.inward, SpiderLegEnd.outward].filterMap (fun delta =>
      if j == m + 1 ∧ SpiderLegEnd.free ≠ SpiderLegEnd.free ∧ delta ≠ SpiderLegEnd.free then none
      else
        let d := spider_rho (m + 1 - j) delta SpiderLegEnd.free
        if j ≥ 2 then
          let new_L := (j - 1, delta) :: rest
          some (d ^^^ spider_gamma (m + 1 + 1) CentreStatus.incoming new_L)
        else
          let new_s := spider_update_centre CentreStatus.incoming delta
          some (d ^^^ spider_gamma (m + 1 + 1) new_s rest)
    )) =
    (let j := idx + 2
     let d := m + 1 - j
     [SpiderLegEnd.inward, SpiderLegEnd.outward].map (fun delta =>
       d ^^^ spider_gamma (m + 1 + 1) CentreStatus.incoming [(idx + 1, delta), (1, SpiderLegEnd.free)]
     )) := by
    intro idx
    dsimp
    simp
    exact ⟨rfl, rfl⟩

  change (let rest := [(m + 1, SpiderLegEnd.free)]
    (List.range 1).flatMap (fun j_zero =>
      let j := j_zero + 1
      [SpiderLegEnd.inward, SpiderLegEnd.outward].filterMap (fun delta =>
        if j == 1 ∧ SpiderLegEnd.free ≠ SpiderLegEnd.free ∧ delta ≠ SpiderLegEnd.free then none
        else
          let d := spider_rho (1 - j) delta SpiderLegEnd.free
          if j ≥ 2 then
            let new_L := (j - 1, delta) :: rest
            some (d ^^^ spider_gamma (m + 1 + 1) CentreStatus.incoming new_L)
          else
            let new_s := spider_update_centre CentreStatus.incoming delta
            some (d ^^^ spider_gamma (m + 1 + 1) new_s rest)
      ))) ++
    ((let rest := [(1, SpiderLegEnd.free)]
    (List.range (m + 1)).flatMap (fun j_zero =>
      let j := j_zero + 1
      [SpiderLegEnd.inward, SpiderLegEnd.outward].filterMap (fun delta =>
        if j == m + 1 ∧ SpiderLegEnd.free ≠ SpiderLegEnd.free ∧ delta ≠ SpiderLegEnd.free then none
        else
          let d := spider_rho (m + 1 - j) delta SpiderLegEnd.free
          if j ≥ 2 then
            let new_L := (j - 1, delta) :: rest
            some (d ^^^ spider_gamma (m + 1 + 1) CentreStatus.incoming new_L)
          else
            let new_s := spider_update_centre CentreStatus.incoming delta
            some (d ^^^ spider_gamma (m + 1 + 1) new_s rest)
      ))) ++ []) = _
  rw [List.append_nil]
  rw [H0]
  have Hrange : List.range (m + 1) = 0 :: List.map Nat.succ (List.range m) := List.range_succ_eq_map
  rw [Hrange]
  rw [List.flatMap_cons]
  rw [List.flatMap_map]
  have Hmap : (List.range m).flatMap (fun a => (let rest := [(1, SpiderLegEnd.free)]
    let j_zero := a.succ
    let j := j_zero + 1
    [SpiderLegEnd.inward, SpiderLegEnd.outward].filterMap (fun delta =>
      if j == m + 1 ∧ SpiderLegEnd.free ≠ SpiderLegEnd.free ∧ delta ≠ SpiderLegEnd.free then none
      else
        let d := spider_rho (m + 1 - j) delta SpiderLegEnd.free
        if j ≥ 2 then
          let new_L := (j - 1, delta) :: rest
          some (d ^^^ spider_gamma (m + 1 + 1) CentreStatus.incoming new_L)
        else
          let new_s := spider_update_centre CentreStatus.incoming delta
          some (d ^^^ spider_gamma (m + 1 + 1) new_s rest)
    ))) =
    (List.range m).flatMap (fun idx =>
      let j := idx + 2
      let d := m + 1 - j
      [SpiderLegEnd.inward, SpiderLegEnd.outward].map (fun delta =>
        d ^^^ spider_gamma (m + 1 + 1) CentreStatus.incoming [(idx + 1, delta), (1, SpiderLegEnd.free)]
      )) := by
    have h_eq : (fun a => (let rest := [(1, SpiderLegEnd.free)]
      let j_zero := a.succ
      let j := j_zero + 1
      [SpiderLegEnd.inward, SpiderLegEnd.outward].filterMap (fun delta =>
        if j == m + 1 ∧ SpiderLegEnd.free ≠ SpiderLegEnd.free ∧ delta ≠ SpiderLegEnd.free then none
        else
          let d := spider_rho (m + 1 - j) delta SpiderLegEnd.free
          if j ≥ 2 then
            let new_L := (j - 1, delta) :: rest
            some (d ^^^ spider_gamma (m + 1 + 1) CentreStatus.incoming new_L)
          else
            let new_s := spider_update_centre CentreStatus.incoming delta
            some (d ^^^ spider_gamma (m + 1 + 1) new_s rest)
      ))) =
      (fun idx =>
        let j := idx + 2
        let d := m + 1 - j
        [SpiderLegEnd.inward, SpiderLegEnd.outward].map (fun delta =>
          d ^^^ spider_gamma (m + 1 + 1) CentreStatus.incoming [(idx + 1, delta), (1, SpiderLegEnd.free)]
        )) := by
      funext idx
      exact H1_succ idx
    rw [h_eq]
  rw [Hmap]
  rw [H1_0]
  simp
