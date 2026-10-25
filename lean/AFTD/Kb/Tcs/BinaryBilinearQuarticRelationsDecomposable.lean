import AFTD.Prelude

/-!
# binary_bilinear_quartic_relations_decomposable

Topic: quantum   Node: 7e653ead5074

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

A binary bilinear form satisfying all four-index alternating relations is the sum of two swapped products of linear functionals.
-/

theorem binary_bilinear_quartic_relations_decomposable {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V)
    (hP : ∀ v w y z, B v w * B y z + B v y * B w z + B v z * B w y = 0) :
    ∃ a b : V →ₗ[ZMod 2] ZMod 2, ∀ v w, B v w = a v*b w+b v*a w := by
  classical
  by_cases hz : ∀ v w, B v w = 0
  · exact ⟨0,0, by simp [hz]⟩
  · push Not at hz
    obtain ⟨k,l,hkl⟩ := hz
    have h01 : ∀ t : ZMod 2, t=0 ∨ t=1 := by decide
    have hkl1 : B k l=1 := (h01 _).resolve_left hkl
    refine ⟨B.flip k, B.flip l, ?_⟩
    intro v w
    have h := hP v w k l
    rw [hkl1, mul_one] at h
    have he : B v w = -(B v k*B w l+B v l*B w k) :=
      eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using h)
    change B v w = B v k*B w l+B v l*B w k
    simpa only [CharTwo.neg_eq] using he
