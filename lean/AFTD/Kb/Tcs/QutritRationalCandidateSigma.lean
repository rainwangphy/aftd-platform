import AFTD.Prelude

/-!
# qutrit_rational_candidate_sigma

Topic: quantum   Node: 2f52fd220679

Provenance: helper lemma. OP-2299; exact rational two-copy PPT bosonic extension, experiments 40204 and 40206.

The explicit rational density-matrix candidate from the two-copy extension computation.
-/

noncomputable def qutrit_rational_candidate_sigma : Matrix (Fin 3) (Fin 3) ℂ := !![((17581297 : ℂ) / 60000000), (((-6609577 : ℂ) / 200000000) + ((1261389 : ℂ) / 10000000) * Complex.I), (((-7301359 : ℂ) / 100000000) + ((543 : ℂ) / 10000) * Complex.I);
    (((-6609577 : ℂ) / 200000000) + ((-1261389 : ℂ) / 10000000) * Complex.I), ((17891393 : ℂ) / 120000000), (((-23011073 : ℂ) / 200000000) + ((-179009 : ℂ) / 6250000) * Complex.I);
    (((-7301359 : ℂ) / 100000000) + ((-543 : ℂ) / 10000) * Complex.I), (((-23011073 : ℂ) / 200000000) + ((179009 : ℂ) / 6250000) * Complex.I), ((66946013 : ℂ) / 120000000)]
