import AFTD.Prelude
import AFTD.Kb.Tcs.WildValidTripleExistsInSix

/-!
# wild_valid_triples_with_reservoir

Topic: graphs   Node: cb94ec542473

Provenance: helper lemma. IN-342 supporting steps for OP-306, arXiv:2610.22142 Sections3.3.2/6. The target remains prescribed-coloring sharpness; these are local validity and conditioning-family helpers, not a seal-free partition theorem or new wild-number bound. No research advance is claimed.

For every finite injectively indexed set of 3q+r vertices, with r at least three, a normalized symmetric row-injective array admits a permutation whose first q consecutive triples are all valid. The final r vertices are unconstrained. This is a validity packing statement, not color connectivity.
-/

private lemma wild_valid_triples_with_reservoir_e_inl {N M : ℕ} (hN : N = 3 + M) (j : Fin 3) (hj : (j:ℕ) < N) :
    finSumFinEquiv.symm (finCongr hN (⟨(j:ℕ), hj⟩ : Fin N)) = Sum.inl j := by
  have hcast : (⟨(j:ℕ), hj⟩ : Fin N) = Fin.cast (by omega : 3 + M = N) (Fin.castAdd M j) := by ext; simp
  rw [hcast]
  simp

private lemma wild_valid_triples_with_reservoir_e_inr {N M : ℕ} (hN : N = 3 + M) (j : Fin M) (hj : 3 + (j:ℕ) < N) :
    finSumFinEquiv.symm (finCongr hN (⟨3 + (j:ℕ), hj⟩ : Fin N)) = Sum.inr j := by
  have hcast : (⟨3 + (j:ℕ), hj⟩ : Fin N) = Fin.cast (by omega : 3 + M = N) (Fin.natAdd 3 j) := by ext; simp
  rw [hcast]
  simp

private def wild_valid_triples_with_reservoir_sel_val {α : Type*} [DecidableEq α] (a b c : α) (t : Fin 3) : α :=
  if t = 0 then a else if t = 1 then b else c

private def wild_valid_triples_with_reservoir_sel_inv {α : Type*} [DecidableEq α] (a b _c : α) (x : α) : Fin 3 :=
  if x = a then 0 else if x = b then 1 else 2

private noncomputable def wild_valid_triples_with_reservoir_sel_equiv
    {α : Type*} [DecidableEq α] (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Fin 3 ≃ {x : α // x ∈ ({a,b,c} : Finset α)} where
  toFun t := ⟨wild_valid_triples_with_reservoir_sel_val a b c t, by
    dsimp [wild_valid_triples_with_reservoir_sel_val]
    split_ifs <;> simp [*]⟩
  invFun x := wild_valid_triples_with_reservoir_sel_inv a b c (x : α)
  left_inv := by
    intro t
    fin_cases t <;> simp [wild_valid_triples_with_reservoir_sel_val,
      wild_valid_triples_with_reservoir_sel_inv, hab, hab.symm, hac, hac.symm, hbc, hbc.symm]
  right_inv := by
    intro x
    rcases x with ⟨x, hx⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxa | hxb | hxc
    · subst x
      apply Subtype.ext
      simp [wild_valid_triples_with_reservoir_sel_val, wild_valid_triples_with_reservoir_sel_inv, hab]
    · subst x
      apply Subtype.ext
      by_cases hba : b = a
      · exact (hab hba.symm).elim
      · simp [wild_valid_triples_with_reservoir_sel_val, wild_valid_triples_with_reservoir_sel_inv, hba]
    · subst x
      apply Subtype.ext
      by_cases hca : c = a
      · exact (hac hca.symm).elim
      · by_cases hcb : c = b
        · exact (hbc hcb.symm).elim
        · simp [wild_valid_triples_with_reservoir_sel_val, wild_valid_triples_with_reservoir_sel_inv, hca, hcb]

theorem wild_valid_triples_with_reservoir {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (q r : ℕ) (hr : 3≤r) (v : Fin (3*q+r) → C) (hv : Function.Injective v) :
    ∃ σ : Equiv.Perm (Fin (3*q+r)),∀ t : Fin (q),
      A (v (σ ⟨3*t.val+0,by omega⟩)) (v (σ ⟨3*t.val+1,by omega⟩))≠(v (σ ⟨3*t.val+2,by omega⟩)) ∧ A (v (σ ⟨3*t.val+0,by omega⟩)) (v (σ ⟨3*t.val+2,by omega⟩))≠(v (σ ⟨3*t.val+1,by omega⟩)) ∧ A (v (σ ⟨3*t.val+1,by omega⟩)) (v (σ ⟨3*t.val+2,by omega⟩))≠(v (σ ⟨3*t.val+0,by omega⟩)) := by
  induction q with
  | zero =>
      exact ⟨Equiv.refl _, by intro t; exact Fin.elim0 t⟩
  | succ q ih =>
      let N := 3 * (q + 1) + r
      let M := 3 * q + r
      have hN : N = 3 + M := by dsimp [N, M]; omega
      have hN6 : 6 ≤ N := by dsimp [N]; omega
      let e6 : Fin 6 → Fin N := Fin.castLE hN6
      have he6 : Function.Injective e6 := Fin.castLE_injective hN6
      have hw6 : Function.Injective (fun i : Fin 6 => v (e6 i)) := hv.comp he6
      obtain ⟨i, j, k, hij, hik, hjk, h1, h2, h3⟩ :=
        wild_valid_triple_exists_in_six A hinj (fun i : Fin 6 => v (e6 i)) hw6
      let a : Fin N := e6 i
      let b : Fin N := e6 j
      let c : Fin N := e6 k
      have hab : a ≠ b := by
        intro h; apply hij; exact he6 h
      have hac : a ≠ c := by
        intro h; apply hik; exact he6 h
      have hbc : b ≠ c := by
        intro h; apply hjk; exact he6 h
      have htriple1 : A (v a) (v b) ≠ v c := by simpa [a, b, c] using h1
      have htriple2 : A (v a) (v c) ≠ v b := by simpa [a, b, c] using h2
      have htriple3 : A (v b) (v c) ≠ v a := by simpa [a, b, c] using h3
      let S : Finset (Fin N) := {a, b, c}
      have hScard : S.card = 3 := by
        simp [S, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
      let T := {x : Fin N // x ∉ S}
      have hTcard : Fintype.card T = M := by
        dsimp [T]
        rw [Fintype.card_subtype_compl]
        have hScard' : Fintype.card {x : Fin N // x ∈ S} = 3 := by
          rw [Fintype.card_coe]
          exact hScard
        rw [hScard', Fintype.card_fin]
        dsimp [N, M] at hN ⊢
        omega
      let eC : T ≃ Fin M := Fintype.equivFinOfCardEq hTcard
      let w : Fin M → C := fun s => v (eC.symm s)
      have hw : Function.Injective w := by
        intro x y hxy
        exact eC.symm.injective (Subtype.ext (hv hxy))
      obtain ⟨τ, hτ⟩ := ih w hw
      let sel : Fin 3 ≃ S := wild_valid_triples_with_reservoir_sel_equiv a b c hab hac hbc
      let e : Fin N ≃ Fin 3 ⊕ Fin M := (finCongr hN).trans finSumFinEquiv.symm
      let eR : Fin M ≃ T := τ.trans eC.symm
      let F : Fin N ≃ Fin N := e.trans ((Equiv.sumCongr sel eR).trans (Equiv.sumCompl (fun x : Fin N => x ∈ S)))
      use F
      intro t
      have hF_inl : ∀ j : Fin 3, F ⟨(j : ℕ), by omega⟩ = (sel j : Fin N) := by
        intro j
        dsimp only [F, e]
        simp only [Equiv.trans_apply]
        rw [wild_valid_triples_with_reservoir_e_inl hN j (by omega)]
        exact Equiv.sumCompl_apply_inl (sel j)
      have hF_inr : ∀ j : Fin M, F ⟨3 + (j : ℕ), by omega⟩ = (eC.symm (τ j) : Fin N) := by
        intro j
        dsimp only [F, e, eR]
        simp only [Equiv.trans_apply]
        rw [wild_valid_triples_with_reservoir_e_inr hN j (by omega)]
        exact Equiv.sumCompl_apply_inr (eC.symm (τ j))
      have hsel0 : (sel (0 : Fin 3) : Fin N) = a := by
        simp [sel, wild_valid_triples_with_reservoir_sel_equiv, wild_valid_triples_with_reservoir_sel_val]
      have hsel1 : (sel (1 : Fin 3) : Fin N) = b := by
        simp [sel, wild_valid_triples_with_reservoir_sel_equiv, wild_valid_triples_with_reservoir_sel_val]
      have hsel2 : (sel (2 : Fin 3) : Fin N) = c := by
        simp [sel, wild_valid_triples_with_reservoir_sel_equiv, wild_valid_triples_with_reservoir_sel_val]
      rcases Fin.eq_zero_or_eq_succ t with rfl | ⟨t', rfl⟩
      · have hF0 : F ⟨3 * (0 : Fin (q + 1)).val + 0, by omega⟩ = a := by
          simpa [hsel0] using hF_inl (0 : Fin 3)
        have hF1 : F ⟨3 * (0 : Fin (q + 1)).val + 1, by omega⟩ = b := by
          simpa [hsel1] using hF_inl (1 : Fin 3)
        have hF2 : F ⟨3 * (0 : Fin (q + 1)).val + 2, by omega⟩ = c := by
          simpa [hsel2] using hF_inl (2 : Fin 3)
        simpa [hF0, hF1, hF2] using ⟨htriple1, htriple2, htriple3⟩
      · have hF0 : F ⟨3 * (t'.val + 1), by omega⟩ = (eC.symm (τ ⟨3 * t'.val + 0, by omega⟩) : Fin N) := by
          have hidx : (⟨3 * (t'.val + 1), by omega⟩ : Fin N) = ⟨3 + (⟨3 * t'.val + 0, by omega⟩ : Fin M).val, by omega⟩ := by
            ext
            simp only [Fin.val_succ]
            omega
          rw [hidx]
          exact hF_inr ⟨3 * t'.val + 0, by omega⟩
        have hF1 : F ⟨3 * (t'.val + 1) + 1, by omega⟩ = (eC.symm (τ ⟨3 * t'.val + 1, by omega⟩) : Fin N) := by
          have hidx : (⟨3 * (t'.val + 1) + 1, by omega⟩ : Fin N) = ⟨3 + (⟨3 * t'.val + 1, by omega⟩ : Fin M).val, by omega⟩ := by
            ext
            simp only [Fin.val_succ]
            omega
          rw [hidx]
          exact hF_inr ⟨3 * t'.val + 1, by omega⟩
        have hF2 : F ⟨3 * (t'.val + 1) + 2, by omega⟩ = (eC.symm (τ ⟨3 * t'.val + 2, by omega⟩) : Fin N) := by
          have hidx : (⟨3 * (t'.val + 1) + 2, by omega⟩ : Fin N) = ⟨3 + (⟨3 * t'.val + 2, by omega⟩ : Fin M).val, by omega⟩ := by
            ext
            simp only [Fin.val_succ]
            omega
          rw [hidx]
          exact hF_inr ⟨3 * t'.val + 2, by omega⟩
        simpa [w, hF0, hF1, hF2] using hτ t'
