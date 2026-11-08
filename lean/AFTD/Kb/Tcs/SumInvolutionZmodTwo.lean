import AFTD.Prelude
import AFTD.Kb.Tcs.F

/-!
# sum_involution_zmod_two

Topic: quantum   Node: 35fc27516c64

Provenance: helper lemma. arXiv:2610.04621 Lemma 5 proof (Appendix B)

For any finite type α with decidable equality, an involution σ : α → α satisfying σ (σ x) = x for all x, and any function f : α → F 2 satisfying f (σ x) = f x for all x, the sum of f x over all x in α equals the sum of f x over all x such that σ x = x.
-/

/-- Sum of a function over a finite type over F_2 reduces to fixed points of an involution. -/
theorem sum_involution_zmod_two {α : Type*} [Fintype α] [DecidableEq α]
    (σ : α → α) (hσ : ∀ x, σ (σ x) = x)
    (f : α → F 2) (hf : ∀ x, f (σ x) = f x) :
    ∑ x, f x = ∑ x ∈ Finset.filter (fun x => σ x = x) Finset.univ, f x := by
  classical
  have hzero : ∑ x ∈ Finset.univ.filter (fun x => σ x ≠ x), f x = 0 := by
    refine Finset.sum_involution (s := Finset.univ.filter (fun x => σ x ≠ x)) (f := f)
      (fun x _ => σ x) ?_ ?_ ?_ ?_
    · intro x hx
      rw [hf x]
      exact CharTwo.add_self_eq_zero (f x)
    · intro x hx hfx
      simpa using hx
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [hσ x]
      exact fun h => hx h.symm
    · intro x hx
      exact hσ x
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun x => σ x = x) (f := f)
  rw [← hsplit, hzero, add_zero]
