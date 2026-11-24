import AFTD.Prelude

/-!
# finite_odd_fibers_coalesce_into_exactly

Topic: graphs   Node: ecceb3d0bd44

Provenance: helper lemma. OP-1957, grouping odd graph components

If a finite map has at least s odd fibers, s is positive, and its domain cardinal has the same parity as s, its fibers can be coalesced into exactly s odd groups without splitting any fiber.
-/

set_option maxHeartbeats 3000000

theorem finite_odd_fibers_coalesce_into_exactly (V I : Type*) [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] (g : V → I) (s : ℕ) (hs : 1 ≤ s) (hodd : s ≤ (Finset.univ.filter (fun i : I => Odd ((Finset.univ.filter (fun v : V => g v = i)).card))).card) (hpar : Fintype.card V % 2 = s % 2) : ∃ f : V → Fin s, (∀ i : Fin s, Odd ((Finset.univ.filter (fun v => f v = i)).card)) ∧ (∀ u v, g u = g v → f u = f v) := by
  classical
  cases s with
  | zero => omega
  | succ m =>
    let O : Finset I := Finset.univ.filter (fun i => Odd ((Finset.univ.filter (fun v : V => g v = i)).card))
    change m+1 ≤ O.card at hodd
    obtain ⟨J,hJO,hJcard⟩ := Finset.exists_subset_card_eq (s := O) (n := m) (by omega)
    have hJodd : ∀ i ∈ J, Odd ((Finset.univ.filter (fun v : V => g v = i)).card) := by
      intro i hi
      exact (Finset.mem_filter.mp (hJO hi)).2
    let e : J ≃ Fin m := Finset.equivFinOfCardEq hJcard
    let f : V → Fin (m+1) := fun v => if hv : g v ∈ J then (e ⟨g v,hv⟩).succ else 0
    let S : Finset V := Finset.univ.filter (fun v => g v ∈ J)
    have hsum : (∑ i ∈ J, (Finset.univ.filter (fun v : V => g v = i)).card) = S.card := by
      simpa [S] using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset V) J g
    have hSmod : S.card % 2 = m % 2 := by
      have hfilter : J.filter (fun i => Odd ((Finset.univ.filter (fun v : V => g v = i)).card)) = J :=
        Finset.filter_eq_self.mpr hJodd
      have ho : Odd S.card ↔ Odd J.card := by
        rw [← hsum, Finset.odd_sum_iff_odd_card_odd, hfilter]
      rw [hJcard] at ho
      simp only [Nat.odd_iff] at ho
      have h1 := Nat.mod_lt S.card (by omega : 0 < 2)
      have h2 := Nat.mod_lt m (by omega : 0 < 2)
      omega
    have hzero : (Finset.univ.filter (fun v : V => f v = 0)) = Finset.univ \ S := by
      ext v
      by_cases hv : g v ∈ J <;> simp [f,S,hv]
    have hzeroOdd : Odd ((Finset.univ.filter (fun v : V => f v = 0)).card) := by
      apply Nat.odd_iff.mpr
      rw [hzero,Finset.card_sdiff_of_subset (Finset.subset_univ S),Finset.card_univ]
      have hle : S.card ≤ Fintype.card V := by simpa using Finset.card_le_univ S
      omega
    refine ⟨f, ?_, ?_⟩
    · intro i
      refine Fin.cases hzeroOdd ?_ i
      intro j
      let x : J := e.symm j
      have hex : e x = j := e.apply_symm_apply j
      have hfiber : (Finset.univ.filter (fun v : V => f v = j.succ)) =
          Finset.univ.filter (fun v : V => g v = x.val) := by
        ext v
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        by_cases hv : g v ∈ J
        · simp only [f,hv,dif_pos,Fin.succ_inj]
          constructor
          · intro h
            have hh : (⟨g v,hv⟩ : J) = x := e.injective (by simpa [hex] using h)
            exact congrArg Subtype.val hh
          · intro hg
            have hh : (⟨g v,hv⟩ : J) = x := Subtype.ext hg
            simpa [hh] using hex
        · have hneq : g v ≠ x.val := by
            intro hh
            apply hv
            simpa [hh] using x.property
          have hj0 : (0 : Fin (m+1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
          simp [f,hv,hneq,hj0]
      rw [hfiber]
      exact hJodd x.val x.property
    · intro u v huv
      by_cases hu : g u ∈ J
      · have hv : g v ∈ J := by simpa [← huv] using hu
        simp only [f,hu,hv,dif_pos]
        congr 2
        exact Subtype.ext huv
      · have hv : g v ∉ J := by simpa [← huv] using hu
        simp [f,hu,hv]
