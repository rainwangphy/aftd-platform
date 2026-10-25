import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryQuadraticPolarQuarticRelation
import AFTD.Kb.Tcs.BinaryBilinearQuarticRelationsDecomposable

/-!
# binary_quadratic_decomposable_mod_linear_of_fourth_difference

Topic: quantum   Node: ce79c14c7e9d

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

If twice the binary lift of a quadratic form has vanishing fourth differences on all cubes, the form is one product of two linear forms plus a linear form.
-/

theorem binary_quadratic_decomposable_mod_linear_of_fourth_difference {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V)
    (hfour : ∀ u : Fin 4 → V,
      (∑ x : Fin 4 → ZMod 2,
        (-1 : ZMod 8) ^ (∑ i : Fin 4, (x i).val) *
          (2 * ((Q (∑ i : Fin 4, x i • u i)).val : ZMod 8))) = 0) :
    ∃ a b l : V →ₗ[ZMod 2] ZMod 2, ∀ v, Q v = a v*b v+l v := by
  obtain ⟨a,b,hab⟩ := binary_bilinear_quartic_relations_decomposable Q.polarBilin
    (binary_quadratic_polar_quartic_relation Q hfour)
  let l : V →ₗ[ZMod 2] ZMod 2 := {
    toFun := fun x => Q x-a x*b x
    map_add' := by
      intro x y
      simp only [QuadraticMap.map_add Q, ← QuadraticMap.polarBilin_apply_apply,
        map_add, hab]
      ring
    map_smul' := by
      intro c x
      have hc : c*c=c := by
        have hh : ∀ t : ZMod 2, t*t=t := by decide
        exact hh c
      change Q (c • x)-a (c • x)*b (c • x)=c*(Q x-a x*b x)
      simp only [QuadraticMap.map_smul Q, map_smul, smul_eq_mul]
      calc
        (c*c)*Q x-(c*a x)*(c*b x)=(c*c)*(Q x-a x*b x) := by ring
        _ = c*(Q x-a x*b x) := by rw [hc]
  }
  refine ⟨a,b,l,?_⟩
  intro x
  change Q x=a x*b x+(Q x-a x*b x)
  ring
