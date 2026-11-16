import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialNullityPoly
import AFTD.Kb.Tcs.PetrialMatrix

/-!
# petrial_nullity_poly_empty_induced

Topic: combinatorics   Node: 21b0496f25ce

Provenance: helper lemma. Empty base case for the OP-1239 leaf-deletion certificate.

The partial Petrial nullity generating polynomial of the empty induced graph is one.
-/

theorem petrial_nullity_poly_empty_induced {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : petrial_nullity_poly (G.induce (∅ : Set V)) = 1 := by
  unfold petrial_nullity_poly
  have hcard : Fintype.card (↥(∅ : Set V)) = 0 := Fintype.card_eq_zero
  have hterm : ∀ F : Finset (↥(∅ : Set V)), (Polynomial.X : Polynomial ℕ) ^ (Fintype.card (↥(∅ : Set V)) - (petrial_matrix (G.induce (∅ : Set V)) F).rank) = 1 := by
    intro F
    rw [hcard, Nat.zero_sub, pow_zero]
  simp_rw [hterm]
  have : (Finset.univ : Finset (Finset (↥(∅ : Set V)))) = {∅} := by
    ext F
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    ext x
    exact IsEmpty.elim inferInstance x
  rw [this]
  simp
