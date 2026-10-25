import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeHadamardCleanReturnPhases

/-!
# three_hadamard_clean_return_phase_sq

Topic: quantum   Node: 94e52732bbad

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

Under clean return of the three-Hadamard chain, its returning amplitude (1+u+v-u*v)/(2*sqrt(2)) has square u.
-/

theorem three_hadamard_clean_return_phase_sq (u v : ℂ)
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hreturn : 1 - u + v + u * v = 0) :
    ((1 + u + v - u * v) / (2 * (Real.sqrt 2 : ℂ))) ^ 2 = u := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rcases three_hadamard_clean_return_phases u v hu hv hreturn with ⟨rfl, h | h⟩
  all_goals
    rw [h]
    rw [div_pow, mul_pow, hs]
    norm_num [Complex.I_sq]
    ring_nf
    norm_num [Complex.I_sq]
  all_goals ring
