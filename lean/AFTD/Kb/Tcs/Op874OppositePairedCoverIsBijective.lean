import AFTD.Prelude

/-!
# op874_opposite_paired_cover_is_bijective

Topic: graphs   Node: 2ce2b167dd8d

Provenance: helper lemma. Structural reduction for the exact-owner global-pair route to OP-874; experiment 43048 tests the hypotheses.

For a finite set split into two classes by a fixed-point-free class-switching involution, any map for which each true vertex has a false preimage restricts to a bijection from the false vertices onto the true vertices.
-/

theorem op874_opposite_paired_cover_is_bijective {V : Type*} [Fintype V] [DecidableEq V]
    (flag : V → Bool) (mate own : V → V)
    (hmate : ∀ v, mate (mate v) = v)
    (hflip : ∀ v, flag (mate v) = !flag v)
    (hcover : ∀ p, flag p = true → ∃ q, flag q = false ∧ own q = p) :
    ∀ q, flag q = false → flag (own q) = true ∧
      ∀ r, flag r = false → own r = own q → r = q := by
  classical
  let P := {v : V // flag v = true}
  let Q := {v : V // flag v = false}
  let eqv : P ≃ Q :=
    { toFun := fun p => ⟨mate p.1, by simp [hflip, p.2]⟩
      invFun := fun q => ⟨mate q.1, by simp [hflip, q.2]⟩
      left_inv := fun p => Subtype.ext (hmate p.1)
      right_inv := fun q => Subtype.ext (hmate q.1) }
  have hcard : Fintype.card P = Fintype.card Q := Fintype.card_congr eqv
  let choose : P → Q := fun p => ⟨Classical.choose (hcover p.1 p.2),
    (Classical.choose_spec (hcover p.1 p.2)).1⟩
  have hchoose : ∀ p : P, own (choose p).1 = p.1 := fun p =>
    (Classical.choose_spec (hcover p.1 p.2)).2
  have hinj : Function.Injective choose := by
    intro p r h
    apply Subtype.ext
    have h' := congrArg (fun q : Q => own q.1) h
    simpa only [hchoose] using h'
  have hsurj : Function.Surjective choose :=
    (Fintype.bijective_iff_injective_and_card choose).2 ⟨hinj, hcard⟩ |>.2
  intro q hq
  obtain ⟨p, hp⟩ := hsurj ⟨q,hq⟩
  have hval : (choose p).1 = q := congrArg Subtype.val hp
  have hown : own q = p.1 := by rw [←hval]; exact hchoose p
  refine ⟨hown ▸ p.2, ?_⟩
  intro r hr heq
  obtain ⟨s, hs⟩ := hsurj ⟨r,hr⟩
  have hval' : (choose s).1 = r := congrArg Subtype.val hs
  have hown' : own r = s.1 := by rw [←hval']; exact hchoose s
  have hps : p = s := Subtype.ext (by rw [← hown, ← hown']; exact heq.symm)
  subst s
  exact hval'.symm.trans hval
