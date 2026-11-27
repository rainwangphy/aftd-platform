import AFTD.Prelude

/-!
# op309_girth8_voltage_signature_zero_cycle

Topic: graphs   Node: a81ab1db363a

Provenance: helper lemma. OP-309 source-forest cover analysis, experiments 42324–42325 and 42351.

If the two indicated host-signature residues agree, the signed voltage of the listed eight-cycle is zero.
-/

theorem op309_girth8_voltage_signature_zero_cycle (a b c d m : ℤ)
    (h : (-a-b) % m = (-c+d) % m) : (a+b+d-c) % m = 0 := by
  have h1 : ((-a-b) - (-c+d)) % m = 0 := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h
  have h2 : m ∣ ((-a-b) - (-c+d)) := Int.dvd_of_emod_eq_zero h1
  have h3 : m ∣ -((-a-b) - (-c+d)) := dvd_neg.mpr h2
  have h4 : -((-a-b) - (-c+d)) = a+b+d-c := by ring
  rw [h4] at h3
  exact Int.emod_eq_zero_of_dvd h3
