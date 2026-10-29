import AFTD.Prelude
import AFTD.Kb.Tcs.WildValidTripleExistsInSix
import AFTD.Kb.Tcs.WildValidTriplesNineRepair
import AFTD.Kb.Tcs.G

/-!
# wild_valid_triples_nine_factor

Topic: graphs   Node: b6b60a5c8344

Provenance: helper lemma. IN-342 supporting steps for OP-306, arXiv:2610.22142 Sections3.3.2/6. The target remains prescribed-coloring sharpness; these are local validity and conditioning-family helpers, not a seal-free partition theorem or new wild-number bound. No research advance is claimed.

Every injective nine-vertex restriction of a normalized symmetric row-injective array can be permuted into three valid triples. The range of the array need not be contained in the nine vertices. This is a local packing helper, not a new wild-number case.
-/

set_option maxHeartbeats 4000000
private def in342_wrap_valid {C : Type*} (A : C → C → C) (x y z : C) : Prop :=
  A x y≠z ∧ A x z≠y ∧ A y z≠x
private theorem in342_wrap_vec_inj {D : Type*} (i j k : D)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    Function.Injective (![i,j,k] : Fin 3 → D) := by
  intro a b h
  fin_cases a <;> fin_cases b
  · rfl
  · change i=j at h
    exact (hij h).elim
  · change i=k at h
    exact (hik h).elim
  · change j=i at h
    exact ((Ne.symm hij) h).elim
  · rfl
  · change j=k at h
    exact (hjk h).elim
  · change k=i at h
    exact ((Ne.symm hik) h).elim
  · change k=j at h
    exact ((Ne.symm hjk) h).elim
  · rfl

private theorem in342_wrap_place {C : Type*} (A : C → C → C)
    (hinj : ∀ x,Function.Injective (A x)) {N : ℕ}
    (v : Fin N → C) (hv : Function.Injective v)
    (ι : Fin 6 → Fin N) (hι : Function.Injective ι)
    (f : Fin 3 → Fin N) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin N),
      in342_wrap_valid A (v (σ (f 0))) (v (σ (f 1))) (v (σ (f 2))) := by
  obtain ⟨i,j,k,hij,hik,hjk,hgood⟩ := wild_valid_triple_exists_in_six A hinj (v ∘ ι) (hv.comp hι)
  let g : Fin 3 → Fin N := ι ∘ (![i,j,k] : Fin 3 → Fin 6)
  have hg : Function.Injective g := hι.comp (in342_wrap_vec_inj i j k hij hik hjk)
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ,?_⟩
  rw [hσ 0,hσ 1,hσ 2]
  exact hgood

private def in342_wrap_slot (t j : Fin 3) : Fin 9 := ⟨3*t.val+j.val,by omega⟩
private def in342_wrap_goal {C : Type*} (A : C → C → C) (v : Fin 9 → C) : Prop :=
  ∃ σ : Equiv.Perm (Fin 9),∀ t : Fin 3,
    in342_wrap_valid A (v (σ (in342_wrap_slot t 0)))
      (v (σ (in342_wrap_slot t 1))) (v (σ (in342_wrap_slot t 2)))

theorem wild_valid_triples_nine_factor {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v) :
    ∃ σ : Equiv.Perm (Fin (9)),∀ t : Fin (3),
      A (v (σ ⟨3*t.val+0,by omega⟩)) (v (σ ⟨3*t.val+1,by omega⟩))≠(v (σ ⟨3*t.val+2,by omega⟩)) ∧ A (v (σ ⟨3*t.val+0,by omega⟩)) (v (σ ⟨3*t.val+2,by omega⟩))≠(v (σ ⟨3*t.val+1,by omega⟩)) ∧ A (v (σ ⟨3*t.val+1,by omega⟩)) (v (σ ⟨3*t.val+2,by omega⟩))≠(v (σ ⟨3*t.val+0,by omega⟩)) := by
  classical
  change in342_wrap_goal A v
  let E : Fin 6 ↪ Fin 9 := Fin.castAddEmb 3
  obtain ⟨σ1,h1⟩ := in342_wrap_place A hinj v hv E E.injective
    (![6,7,8] : Fin 3 → Fin 9) (by decide +kernel)
  change in342_wrap_valid A (v (σ1 6)) (v (σ1 7)) (v (σ1 8)) at h1
  let w : Fin 6 → C := fun i => v (σ1 (E i))
  have hw : Function.Injective w := hv.comp (σ1.injective.comp E.injective)
  obtain ⟨σ2,h2⟩ := in342_wrap_place A hinj w hw (id : Fin 6 → Fin 6) Function.injective_id
    (![3,4,5] : Fin 3 → Fin 6) (by decide +kernel)
  change in342_wrap_valid A (w (σ2 3)) (w (σ2 4)) (w (σ2 5)) at h2
  let lift : Equiv.Perm (Fin 9) := σ2.viaFintypeEmbedding E
  have hcast (i : Fin 6) : lift (E i)=E (σ2 i) :=
    Equiv.Perm.viaFintypeEmbedding_apply_image σ2 E i
  have hfix6 : lift 6=6 := by
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range σ2 E
    rintro ⟨i,hi⟩
    have hh := congrArg Fin.val hi
    change i.val=6 at hh
    omega
  have hfix7 : lift 7=7 := by
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range σ2 E
    rintro ⟨i,hi⟩
    have hh := congrArg Fin.val hi
    change i.val=7 at hh
    omega
  have hfix8 : lift 8=8 := by
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range σ2 E
    rintro ⟨i,hi⟩
    have hh := congrArg Fin.val hi
    change i.val=8 at hh
    omega
  let ρ : Equiv.Perm (Fin 9) := lift.trans σ1
  let v' : Fin 9 → C := fun i => v (ρ i)
  have hv' : Function.Injective v' := hv.comp ρ.injective
  have hT1 : in342_wrap_valid A (v' 3) (v' 4) (v' 5) := by
    change in342_wrap_valid A (v (σ1 (lift (E 3)))) (v (σ1 (lift (E 4)))) (v (σ1 (lift (E 5))))
    rw [hcast 3,hcast 4,hcast 5]
    exact h2
  have hT2 : in342_wrap_valid A (v' 6) (v' 7) (v' 8) := by
    change in342_wrap_valid A (v (σ1 (lift 6))) (v (σ1 (lift 7))) (v (σ1 (lift 8)))
    rw [hfix6,hfix7,hfix8]
    exact h1
  have hfinish (π : Equiv.Perm (Fin 9))
      (hb : A (v' (π 0)) (v' (π 1))=v' (π 2))
      (ht1 : in342_wrap_valid A (v' (π 3)) (v' (π 4)) (v' (π 5)))
      (ht2 : in342_wrap_valid A (v' (π 6)) (v' (π 7)) (v' (π 8))) :
      in342_wrap_goal A v := by
    obtain ⟨τ,hτ⟩ := wild_valid_triples_nine_repair A hdiag hsym hinj (v' ∘ π)
      (hv'.comp π.injective) hb ht1 ht2
    refine ⟨(τ.trans π).trans ρ,?_⟩
    intro t
    exact hτ t
  by_cases hg : in342_wrap_valid A (v' 0) (v' 1) (v' 2)
  · refine ⟨ρ,?_⟩
    intro t
    fin_cases t
    · exact hg
    · exact hT1
    · exact hT2
  have hb : A (v' 0) (v' 1)=v' 2 ∨ A (v' 0) (v' 2)=v' 1 ∨ A (v' 1) (v' 2)=v' 0 := by
    unfold in342_wrap_valid at hg
    tauto
  rcases hb with hb|hb|hb
  · exact hfinish (Equiv.refl _) hb hT1 hT2
  · let π : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,1,3,4,5,6,7,8] : Fin 9 → Fin 9) (by decide +kernel)
    exact hfinish π hb hT1 hT2
  · let π : Equiv.Perm (Fin 9) := Equiv.ofBijective (![1,2,0,3,4,5,6,7,8] : Fin 9 → Fin 9) (by decide +kernel)
    exact hfinish π hb hT1 hT2
