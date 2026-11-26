import AFTD.Prelude
import AFTD.Kb.Tcs.Op874TwoColorPalettesRepeat

/-!
# op874_many_disjoint_palette_collisions

Topic: graphs   Node: 4316527629c1

Provenance: helper lemma. Matching-adversarial factor-word construction for OP-874, https://arxiv.org/abs/2610.41950.

For any finite list of two-color palette assignments on at least twice the list length plus five vertices, choose a disjoint pair for every assignment whose two palettes agree.
-/

theorem op874_many_disjoint_palette_collisions
    {V : Type*} [DecidableEq V] (m : ℕ) (S : Finset V)
    (P : Fin m → V → Finset (Fin 4))
    (hP : ∀ i v, v ∈ S → (P i v).card = 2)
    (hS : 2*m+5 ≤ S.card) :
    ∃ p : Fin m → Finset V,
      (∀ i, p i ⊆ S ∧ (p i).card = 2 ∧
        ∀ u ∈ p i, ∀ v ∈ p i, P i u = P i v) ∧
      (∀ i j, i ≠ j → Disjoint (p i) (p j)) := by
  classical
  induction m generalizing S with
  | zero =>
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  | succ m ih =>
    have hs7 : 7 ≤ S.card := by omega
    obtain ⟨u, hu, v, hv, huv, hp⟩ :=
      op874_two_color_palettes_repeat S (P 0) (fun w hw => hP 0 w hw) hs7
    let T : Finset V := {u,v}
    have hTsub : T ⊆ S := by
      intro x hx
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hTcard : T.card = 2 := by simp [T, huv]
    let S' := S \ T
    have hcard : S'.card + 2 = S.card := by
      dsimp [S']
      rw [Finset.card_sdiff_of_subset hTsub, hTcard]
      have := Finset.card_le_card hTsub
      rw [hTcard] at this
      omega
    have hP' : ∀ (i : Fin m) (v : V), v ∈ S' → (P i.succ v).card = 2 := by
      intro i w hw
      exact hP i.succ w ((Finset.mem_sdiff.mp hw).1)
    have hS' : 2*m+5 ≤ S'.card := by omega
    obtain ⟨q, hq, hqdis⟩ := ih S' (fun i => P i.succ) hP' hS'
    refine ⟨Fin.cons T q, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        refine ⟨hTsub, hTcard, ?_⟩
        intro x hx y hy
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
      · simp only [Fin.cons_succ]
        obtain ⟨hsub, hc, heq⟩ := hq j
        exact ⟨hsub.trans (Finset.sdiff_subset), hc, heq⟩
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij; exact (hij rfl).elim
        · intro _
          simp only [Fin.cons_zero, Fin.cons_succ]
          apply Finset.disjoint_left.mpr
          intro x hx hqmem
          have hxS' := (hq j').1 hqmem
          exact (Finset.mem_sdiff.mp hxS').2 hx
      · intro j
        refine Fin.cases ?_ (fun j' => ?_) j
        · intro _
          simp only [Fin.cons_succ, Fin.cons_zero]
          apply Finset.disjoint_left.mpr
          intro x hx hTmem
          have hxS' := (hq i').1 hx
          exact (Finset.mem_sdiff.mp hxS').2 hTmem
        · intro hij
          simp only [Fin.cons_succ]
          apply hqdis i' j'
          intro heq
          apply hij
          exact congrArg Fin.succ heq
