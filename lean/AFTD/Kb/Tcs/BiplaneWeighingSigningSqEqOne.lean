import AFTD.Prelude
import AFTD.Kb.Tcs.BiplaneWeighingSigning
import AFTD.Kb.Tcs.Biplane
import AFTD.Kb.Tcs.BiplaneFlag

/-!
# biplane_weighing_signing_sq_eq_one

Topic: combinatorics   Node: f38b7e29bcf9

Provenance: helper lemma. Sanity check of biplane_weighing_signing; arXiv:2611.17855 (On configurations that are nearly generalised polygons), Section 2.2.

Every value of a weighing signing of a biplane squares to one.
-/

theorem biplane_weighing_signing_sq_eq_one {P L : Type*} [Fintype P] [Fintype L]
    (B : Biplane P L) (σ : BiplaneFlag B → ℤ) (h : biplane_weighing_signing B σ)
    (f : BiplaneFlag B) : σ f ^ 2 = 1 := by
  rcases h.1 f with h1 | h1 <;> rw [h1] <;> norm_num
