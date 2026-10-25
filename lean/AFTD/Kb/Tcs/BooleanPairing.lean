import AFTD.Prelude

/-!
# boolean_pairing

Topic: quantum   Node: 3b0afe7f74ce

Provenance: helper lemma. step towards stabilizer_campbell_howard_iff_reed_muller

The Boolean inner product of two Boolean functions f, g on (ZMod 2)^s is the sum over all vectors x of f x * g x in ZMod 2.
-/

/-- The Boolean (Hamming) inner product of two Boolean functions on the cube (ZMod 2)^s. -/
noncomputable def boolean_pairing {s : ℕ} (f g : (Fin s → ZMod 2) → ZMod 2) : ZMod 2 := ∑ x, f x * g x
