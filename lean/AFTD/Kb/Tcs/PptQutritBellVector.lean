import AFTD.Prelude

/-!
# ppt_qutrit_bell_vector

Topic: quantum   Node: 01e770822088

Provenance: helper lemma. Helper for OP-693 from arXiv:1405.4502, equations (1), (2), (5); and arXiv:2010.04048, Appendix A.

Four explicit real vectors in two-qutrit space used in the PPT Bell-violation example.
-/

open Matrix
open scoped BigOperators ComplexOrder

noncomputable def ppt_qutrit_bell_vector (l : Fin 4) (p : Fin 3 × Fin 3) : ℂ := let a : ℂ := (Real.sqrt (131 / 2 : ℝ) : ℂ) / 12
 match l.val with
 | 0 => if p = (0, 0) ∨ p = (1, 1) then (Real.sqrt 2 : ℂ)⁻¹ else 0
 | 1 => if p = (0, 1) ∨ p = (1, 0) then a else if p = (0, 2) then 1/60 else if p = (2, 1) then -3/10 else 0
 | 2 => if p = (0, 0) then a else if p = (1, 1) then -a else if p = (1, 2) then 1/60 else if p = (2, 0) then 3/10 else 0
 | _ => if p = (0, 1) then -(Real.sqrt 3 : ℂ)⁻¹ else if p = (1, 0) ∨ p = (2, 2) then (Real.sqrt 3 : ℂ)⁻¹ else 0
