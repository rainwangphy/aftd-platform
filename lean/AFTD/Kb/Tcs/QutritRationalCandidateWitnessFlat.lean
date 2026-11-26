import AFTD.Prelude

/-!
# qutrit_rational_candidate_witness_flat

Topic: quantum   Node: 97861c6e3808

Provenance: helper lemma. OP-2299; candidate witness from computations 39270, 40213 and 40215.

The explicit rational Hermitian product-state witness candidate, indexed in lexicographic order.
-/

noncomputable def qutrit_rational_candidate_witness_flat : Matrix (Fin 9) (Fin 9) ℂ := !![    (((391444 : ℂ) + (0 : ℂ) * Complex.I) / 1000000), 0, 0, 0, 0, (((161946 : ℂ) + (-412193 : ℂ) * Complex.I) / 1000000), 0, (((1900095 : ℂ) + (-163382 : ℂ) * Complex.I) / 1000000), 0;
    0, (((2323322 : ℂ) + (0 : ℂ) * Complex.I) / 1000000), 0, (((221606 : ℂ) + (5511 : ℂ) * Complex.I) / 1000000), 0, 0, 0, 0, (((161946 : ℂ) + (412193 : ℂ) * Complex.I) / 1000000);
    0, 0, (((153 : ℂ) + (0 : ℂ) * Complex.I) / 1000000), 0, (((1900095 : ℂ) + (163382 : ℂ) * Complex.I) / 1000000), 0, (((221606 : ℂ) + (-5511 : ℂ) * Complex.I) / 1000000), 0, 0;
    0, (((221606 : ℂ) + (-5511 : ℂ) * Complex.I) / 1000000), 0, (((153 : ℂ) + (0 : ℂ) * Complex.I) / 1000000), 0, 0, 0, 0, (((1900095 : ℂ) + (163382 : ℂ) * Complex.I) / 1000000);
    0, 0, (((1900095 : ℂ) + (-163382 : ℂ) * Complex.I) / 1000000), 0, (((391444 : ℂ) + (0 : ℂ) * Complex.I) / 1000000), 0, (((161946 : ℂ) + (-412193 : ℂ) * Complex.I) / 1000000), 0, 0;
    (((161946 : ℂ) + (412193 : ℂ) * Complex.I) / 1000000), 0, 0, 0, 0, (((2323322 : ℂ) + (0 : ℂ) * Complex.I) / 1000000), 0, (((221606 : ℂ) + (5511 : ℂ) * Complex.I) / 1000000), 0;
    0, 0, (((221606 : ℂ) + (5511 : ℂ) * Complex.I) / 1000000), 0, (((161946 : ℂ) + (412193 : ℂ) * Complex.I) / 1000000), 0, (((2323322 : ℂ) + (0 : ℂ) * Complex.I) / 1000000), 0, 0;
    (((1900095 : ℂ) + (163382 : ℂ) * Complex.I) / 1000000), 0, 0, 0, 0, (((221606 : ℂ) + (-5511 : ℂ) * Complex.I) / 1000000), 0, (((153 : ℂ) + (0 : ℂ) * Complex.I) / 1000000), 0;
    0, (((161946 : ℂ) + (-412193 : ℂ) * Complex.I) / 1000000), 0, (((1900095 : ℂ) + (-163382 : ℂ) * Complex.I) / 1000000), 0, 0, 0, 0, (((391444 : ℂ) + (0 : ℂ) * Complex.I) / 1000000)]
