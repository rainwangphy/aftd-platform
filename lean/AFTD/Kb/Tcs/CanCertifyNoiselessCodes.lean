import AFTD.Prelude
import AFTD.Kb.Tcs.CertifiesNoiselessCodes

/-!
# can_certify_noiseless_codes

Topic: quantum   Node: 7748846150b8

Provenance: formalization of a published result. Source: arXiv:2610.37347 Discussion and outlook, paragraph 3

A dimension d admits certification of noiseless quantum codes by k binary measurements if there exist a parametrized family of measurement operators M : ℝ → Fin k → Matrix (Fin d) (Fin d) ℂ and a parameter bound s_max : ℝ such that certifies_noiseless_codes M s_max holds.
-/

/-- A dimension d admits certification of noiseless quantum codes by k binary measurements if there exists a parametrized family M and bound s_max such that certifies_noiseless_codes M s_max holds. -/
def can_certify_noiseless_codes (d k : ℕ) : Prop := ∃ (M : ℝ → Fin k → Matrix (Fin d) (Fin d) ℂ) (s_max : ℝ),
    certifies_noiseless_codes M s_max
