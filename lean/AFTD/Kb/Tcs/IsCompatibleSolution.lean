import AFTD.Prelude
import AFTD.Kb.Tcs.IsLinearExtension

/-!
# is_compatible_solution

Topic: algorithms   Node: 9dca82cf0f37

Provenance: formalization of a published result. Source: arXiv:2610.18740 Section 5

A triple (L, e, U) is a compatible solution for a partial order P on Fin n and rank i if L, {e}, and U partition Fin n with |L| = i - 1, and there exists a linear extension T of P that places all elements of L below e and e below all elements of U.
-/

/-- A compatible solution s = (L, e, U) for a partial order P on Fin n at rank i. -/
def is_compatible_solution {n : ℕ} (P : PartialOrder (Fin n)) (i : ℕ)
    (L : Finset (Fin n)) (e : Fin n) (U : Finset (Fin n)) : Prop := open scoped Classical in
  L.card = i - 1 ∧
  e ∉ L ∧ e ∉ U ∧ Disjoint L U ∧
  L ∪ {e} ∪ U = Finset.univ ∧
  ∃ (T : LinearOrder (Fin n)), is_linear_extension P T ∧
    (∀ x ∈ L, @LT.lt (Fin n) T.toLT x e) ∧
    (∀ y ∈ U, @LT.lt (Fin n) T.toLT e y)
