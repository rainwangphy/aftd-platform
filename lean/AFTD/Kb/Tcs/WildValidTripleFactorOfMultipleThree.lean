import AFTD.Prelude
import AFTD.Kb.Tcs.WildValidTriplesNineFactor
import AFTD.Kb.Tcs.WildValidTriplesWithReservoir

/-!
# wild_valid_triple_factor_of_multiple_three

Topic: graphs   Node: 644a57a39d33

Provenance: helper lemma. IN-342 supporting steps for OP-306, arXiv:2610.22142 Sections3.3.2/6. The target remains prescribed-coloring sharpness; these are local validity and conditioning-family helpers, not a seal-free partition theorem or new wild-number bound. No research advance is claimed.

Every injectively indexed set of 3q vertices, with q at least three, in a normalized symmetric row-injective array has a valid triple factor. The colors may lie outside this indexed set. It proves local validity packing, with no claim about seals formed by multiple blocks.
-/

set_option maxHeartbeats 4000000

private def in342_mult_valid {C : Type*} (A : C → C → C) (x y z : C) : Prop :=
  A x y≠z ∧ A x z≠y ∧ A y z≠x

theorem wild_valid_triple_factor_of_multiple_three {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (q : ℕ) (hq : 3≤q) (v : Fin (3*q) → C) (hv : Function.Injective v) :
    ∃ σ : Equiv.Perm (Fin (3*q)),∀ t : Fin q,
      A (v (σ ⟨3*t.val+0,by omega⟩)) (v (σ ⟨3*t.val+1,by omega⟩))≠v (σ ⟨3*t.val+2,by omega⟩) ∧
      A (v (σ ⟨3*t.val+0,by omega⟩)) (v (σ ⟨3*t.val+2,by omega⟩))≠v (σ ⟨3*t.val+1,by omega⟩) ∧
      A (v (σ ⟨3*t.val+1,by omega⟩)) (v (σ ⟨3*t.val+2,by omega⟩))≠v (σ ⟨3*t.val+0,by omega⟩) := by
  classical
  have hlen : 3*(q-3)+9=3*q := by omega
  let e : Fin (3*(q-3)+9) ≃ Fin (3*q) := finCongr hlen
  obtain ⟨σ0,h0⟩ := wild_valid_triples_with_reservoir A hdiag hsym hinj
    (q-3) 9 (by omega) (v ∘ e) (hv.comp e.injective)
  let σ1 : Equiv.Perm (Fin (3*q)) := (e.symm.trans σ0).trans e
  have hσ1 (i : Fin (3*(q-3)+9)) : σ1 (e i)=e (σ0 i) := by simp [σ1]
  have hfirst (t : Fin (q-3)) : in342_mult_valid A
      (v (σ1 ⟨3*t.val,by omega⟩))
      (v (σ1 ⟨3*t.val+1,by omega⟩))
      (v (σ1 ⟨3*t.val+2,by omega⟩)) := by
    have hh := h0 t
    have hidx (j : Fin 3) :
        (⟨3*t.val+j.val,by omega⟩ : Fin (3*q))=e ⟨3*t.val+j.val,by omega⟩ := rfl
    change in342_mult_valid A
      (v (σ1 ⟨3*t.val+(0 : Fin 3).val,by omega⟩))
      (v (σ1 ⟨3*t.val+(1 : Fin 3).val,by omega⟩))
      (v (σ1 ⟨3*t.val+(2 : Fin 3).val,by omega⟩))
    rw [hidx 0,hidx 1,hidx 2,hσ1,hσ1,hσ1]
    exact hh
  let E : Fin 9 ↪ Fin (3*q) :=
    ⟨fun i => ⟨3*(q-3)+i.val,by omega⟩,by
      intro i j h
      apply Fin.ext
      have hi := congrArg Fin.val h
      dsimp at hi
      omega⟩
  let w : Fin 9 → C := v ∘ σ1 ∘ E
  have hw : Function.Injective w := hv.comp (σ1.injective.comp E.injective)
  obtain ⟨τ,hτ⟩ := wild_valid_triples_nine_factor A hdiag hsym hinj w hw
  let lift : Equiv.Perm (Fin (3*q)) := τ.viaFintypeEmbedding E
  have himage (i : Fin 9) : lift (E i)=E (τ i) :=
    Equiv.Perm.viaFintypeEmbedding_apply_image τ E i
  have hfix (t : Fin (q-3)) (j : Fin 3) :
      lift ⟨3*t.val+j.val,by omega⟩=⟨3*t.val+j.val,by omega⟩ := by
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range τ E
    rintro ⟨i,hi⟩
    have hh := congrArg Fin.val hi
    change 3*(q-3)+i.val=3*t.val+j.val at hh
    have ht' := t.isLt
    have hj' := j.isLt
    omega
  refine ⟨lift.trans σ1,?_⟩
  intro t
  change in342_mult_valid A
    (v (σ1 (lift ⟨3*t.val,by omega⟩)))
    (v (σ1 (lift ⟨3*t.val+1,by omega⟩)))
    (v (σ1 (lift ⟨3*t.val+2,by omega⟩)))
  by_cases ht : t.val<q-3
  · let s : Fin (q-3) := ⟨t.val,ht⟩
    have h0 := hfix s 0
    have h1 := hfix s 1
    have h2 := hfix s 2
    change lift ⟨3*t.val,by omega⟩=⟨3*t.val,by omega⟩ at h0
    change lift ⟨3*t.val+1,by omega⟩=⟨3*t.val+1,by omega⟩ at h1
    change lift ⟨3*t.val+2,by omega⟩=⟨3*t.val+2,by omega⟩ at h2
    simpa only [h0,h1,h2] using hfirst s
  · let s : Fin 3 := ⟨t.val-(q-3),by omega⟩
    have hslot (j : Fin 3) :
        (⟨3*t.val+j.val,by omega⟩ : Fin (3*q))=E ⟨3*s.val+j.val,by omega⟩ := by
      apply Fin.ext
      change 3*t.val+j.val=3*(q-3)+(3*(t.val-(q-3))+j.val)
      omega
    have h0 := (congrArg lift (hslot 0)).trans (himage ⟨3*s.val+0,by omega⟩)
    have h1 := (congrArg lift (hslot 1)).trans (himage ⟨3*s.val+1,by omega⟩)
    have h2 := (congrArg lift (hslot 2)).trans (himage ⟨3*s.val+2,by omega⟩)
    change lift ⟨3*t.val,by omega⟩=E (τ ⟨3*s.val,by omega⟩) at h0
    change lift ⟨3*t.val+1,by omega⟩=E (τ ⟨3*s.val+1,by omega⟩) at h1
    change lift ⟨3*t.val+2,by omega⟩=E (τ ⟨3*s.val+2,by omega⟩) at h2
    simpa only [h0,h1,h2,w,Function.comp_def,in342_mult_valid,Nat.add_zero] using hτ s
