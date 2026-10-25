import AFTD.Prelude

/-!
# anf_coeff

Topic: quantum   Node: b19a22b5a0db

Provenance: helper lemma. step towards stabilizer_campbell_howard_iff_reed_muller

The algebraic normal form coefficient of the monomial indexed by the set T in the Boolean function f is the Mobius transform of f over the subsets of T, namely the sum over R ⊆ T of f evaluated at the indicator vector of R.
-/

/-- The coefficient of the monomial of T in the algebraic normal form of f (Mobius transform over subsets of T). -/
noncomputable def anf_coeff {s : ℕ} (f : (Fin s → ZMod 2) → ZMod 2) (T : Finset (Fin s)) : ZMod 2 := ∑ R ∈ T.powerset, f (fun i => if i ∈ R then 1 else 0)
