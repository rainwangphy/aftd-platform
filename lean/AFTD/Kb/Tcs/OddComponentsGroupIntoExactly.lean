import AFTD.Prelude

/-!
# odd_components_group_into_exactly

Topic: graphs   Node: bc7542eaf596

Provenance: helper lemma. OP-1957: grouping odd barrier components.

If a finite graph has at least s odd connected components, s is positive, and the vertex count has the same parity as s, then its vertices partition into exactly s odd anticomplete groups.
-/

set_option maxHeartbeats 3000000

theorem in1158_finite_odd_fibers_local (V I : Type*) [Fintype V] [Fintype I]
    [DecidableEq V] [DecidableEq I] (g : V → I) (s : ℕ) (hs : 1 ≤ s)
    (hodd : s ≤ (Finset.univ.filter (fun i : I => Odd ((Finset.univ.filter (fun v : V => g v = i)).card))).card)
    (hpar : Fintype.card V % 2 = s % 2) :
    ∃ f : V → Fin s, (∀ i : Fin s, Odd ((Finset.univ.filter (fun v => f v = i)).card)) ∧
      (∀ u v, g u = g v → f u = f v) := by
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

theorem odd_components_group_into_exactly
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (s : ℕ) (hs : 1 ≤ s) (hodd : s ≤ H.oddComponents.ncard)
    (hpar : Fintype.card V % 2 = s % 2) :
    ∃ f : V → Fin s,
      (∀ i : Fin s, Odd ((Finset.univ.filter (fun v => f v = i)).card)) ∧
      (∀ u v, f u ≠ f v → ¬ H.Adj u v) := by
  classical
  let g : V → H.ConnectedComponent := H.connectedComponentMk
  have hfiber (c : H.ConnectedComponent) :
      (Finset.univ.filter (fun v : V => g v = c)) = c.supp.toFinset := by
    ext v
    simp [g,SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hset : (Finset.univ.filter (fun c : H.ConnectedComponent =>
      Odd ((Finset.univ.filter (fun v : V => g v = c)).card))) = H.oddComponents.toFinset := by
    ext c
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_toFinset]
    rw [hfiber,← Set.ncard_eq_toFinset_card']
    rfl
  have hodd' : s ≤ (Finset.univ.filter (fun c : H.ConnectedComponent =>
      Odd ((Finset.univ.filter (fun v : V => g v = c)).card))).card := by
    rw [hset,← Set.ncard_eq_toFinset_card']
    exact hodd
  obtain ⟨f,hf,hconst⟩ := in1158_finite_odd_fibers_local V H.ConnectedComponent g s hs hodd' hpar
  refine ⟨f,hf,?_⟩
  intro u v hne hadj
  apply hne
  apply hconst
  exact SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable
