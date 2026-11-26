import AFTD.Prelude
import AFTD.Kb.Tcs.QutritPhaseRoot
import AFTD.Kb.Tcs.QutritCyclicFaceSosTerms
import AFTD.Kb.Tcs.QutritCyclicFaceComplexSos
import AFTD.Kb.Tcs.QutritPhaseRootPolynomial
import AFTD.Kb.Tcs.QutritPhaseRootConjugate

/-!
# qutrit_zero_bell_cyclic_two_copy_sos

Topic: quantum   Node: a0edfabfc467

Provenance: helper lemma. OP-2299 exact Q(ω) operator verification 41079 and polynomial ideal reduction 41080–41082.

On the zero-Bell product face, the cyclic witness times the squared norm of the second factor equals four explicit squares of PPT two-copy type.
-/

theorem qutrit_zero_bell_cyclic_two_copy_sos (x y : Fin 3 → ℂ)
    (hzero : x 0*y 1 + qutrit_phase_root*x 1*y 2 + qutrit_phase_root^2*x 2*y 0 = 0) :
    (∑ i : Fin 3, Complex.normSq (y i)) *
      ((-Complex.normSq (x 0*y 1+x 1*y 2+x 2*y 0) +
         Complex.normSq (x 0*y 1+qutrit_phase_root^2*x 1*y 2+qutrit_phase_root*x 2*y 0))/3 +
        ∑ i : Fin 3, Complex.normSq (x i*y (i+2))) =
      ∑ j : Fin 4, Complex.normSq (qutrit_cyclic_face_sos_terms x y j) := by
  have h := qutrit_cyclic_face_complex_sos qutrit_phase_root
    (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)
    qutrit_phase_root_polynomial qutrit_phase_root_conjugate hzero
  simpa [qutrit_cyclic_face_sos_terms, Fin.sum_univ_three, Fin.sum_univ_four, add_assoc] using h
