import AFTD.Prelude

/-!
# wild_valid_replacement_from_three

Topic: graphs   Node: 83a7d34c633a

Provenance: helper lemma. IN-342 supporting steps for OP-306, arXiv:2610.22142 Sections3.3.2/6. The target remains prescribed-coloring sharpness; these are local validity and conditioning-family helpers, not a seal-free partition theorem or new wild-number bound. No research advance is claimed.

Given a bad pair witness A(x,y)=z, three distinct candidate replacements all different from z cannot all fail the validity inequalities, provided the rows at x and y are injective. This is a local reservoir lemma, not a claim about connectivity.
-/

set_option maxHeartbeats 4000000

theorem wild_valid_replacement_from_three {C : Type*} (A : C → C → C)
    (x y z : C) (hx : Function.Injective (A x)) (hy : Function.Injective (A y))
    (w : Fin 3 → C) (hw : Function.Injective w) (hbad : A x y=z)
    (hout : ∀ i,w i≠z) :
    ∃ i : Fin 3,A x y≠w i ∧ A x (w i)≠y ∧ A y (w i)≠x := by
  classical
  by_contra hnone
  have h (i : Fin 3) : A x (w i)=y ∨ A y (w i)=x := by
    by_cases hi : A x (w i)=y
    · exact Or.inl hi
    · right
      by_contra hj
      apply hnone
      exact ⟨i,by rw [hbad]; exact Ne.symm (hout i),hi,hj⟩
  have hX (i j : Fin 3) (hij : i≠j) : ¬ (A x (w i)=y ∧ A x (w j)=y) := by
    rintro ⟨hi,hj⟩
    exact hij (hw (hx (hi.trans hj.symm)))
  have hY (i j : Fin 3) (hij : i≠j) : ¬ (A y (w i)=x ∧ A y (w j)=x) := by
    rintro ⟨hi,hj⟩
    exact hij (hw (hy (hi.trans hj.symm)))
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hX01 := hX 0 1 (by decide)
  have hX02 := hX 0 2 (by decide)
  have hX12 := hX 1 2 (by decide)
  have hY01 := hY 0 1 (by decide)
  have hY02 := hY 0 2 (by decide)
  have hY12 := hY 1 2 (by decide)
  tauto
