import AFTD.Prelude

/-!
# monomial

Topic: quantum   Node: e4ccd464fb48

Provenance: formalization of a published result. Source: arXiv:2610.09341, Section 3.1

For a natural number s and a finite subset T of Fin s, the monomial associated with T is the function from (Fin s → ZMod 2) to ZMod 2 sending each vector x to the product over i in T of x i in ZMod 2.
-/

/-- The monomial associated with an index set T : Finset (Fin s) as a Boolean function. -/
def monomial {s : ℕ} (T : Finset (Fin s)) : (Fin s → ZMod 2) → ZMod 2 := fun x => ∏ i ∈ T, x i
