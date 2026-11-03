import AFTD.Prelude

/-!
# finite_function_collision_head_pair_injective

Topic: combinatorics   Node: ca975e20621a

Provenance: helper lemma. Collision counting for the small-overlap route to OP-110.

Given an injective tail-head encoding and a map whose fibers have a fixed tail, encoding each nonrepresentative by its tail and the unordered pair of its head with its representative head is injective.
-/

theorem finite_function_collision_head_pair_injective
    (α β γ δ : Type) [DecidableEq δ] (f : α → β) (r : β → α)
    (tail : α → γ) (head : α → δ)
    (hr : ∀ x, f (r (f x)) = f x)
    (htail : ∀ x y, f x = f y → tail x = tail y)
    (hkey : Function.Injective (fun x => (tail x, head x))) :
    Set.InjOn (fun x => (tail x, s(head x, head (r (f x)))))
      {x | r (f x) ≠ x} := by
  intro x hx y hy hxy
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨htail_eq, hpair_eq⟩ := hxy
  simp only [Sym2.eq, Sym2.rel_iff] at hpair_eq
  rcases hpair_eq with ⟨hhead1, -⟩ | ⟨hhead1, -⟩
  · have : (tail x, head x) = (tail y, head y) := Prod.ext htail_eq hhead1
    exact hkey this
  · have htail_rfy : tail (r (f y)) = tail y := htail (r (f y)) y (hr y)
    have hkey_x_rfy : (tail x, head x) = (tail (r (f y)), head (r (f y))) :=
      Prod.ext (htail_eq.trans htail_rfy.symm) hhead1
    have hx_eq_rfy : x = r (f y) := hkey hkey_x_rfy
    have hfx_eq : f x = f y := by rw [hx_eq_rfy, hr y]
    have hrfx_eq_x : r (f x) = x := by rw [hfx_eq, ← hx_eq_rfy]
    exact (hx hrfx_eq_x).elim
