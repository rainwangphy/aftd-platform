import AFTD.Prelude
import AFTD.Kb.Tcs.MixedGraphIsValid
import AFTD.Kb.Tcs.MixedGraphIsRegular

/-!
# mixed_graph_card_ge_of_is_regular

Topic: graphs   Node: 0520d1e0f926

Provenance: formalization of a published result. Source: arXiv:2610.14110 (New mixed cages, bounds and computational results), Theorem 3.1 (the lower bound n(r,z,g) ≥ r + 2z + 1 used for g = 3 in Theorem 5.1; here for every regular mixed graph).

Every (r, z)-regular mixed graph on a finite nonempty vertex set has at least r + 2z + 1 vertices.
-/

theorem mixed_graph_card_ge_of_is_regular {V : Type*} [Fintype V] [Nonempty V]
    (E : SimpleGraph V) (A : V → V → Prop) (r z : ℕ) (hv : mixed_graph_is_valid E A)
    (hr : mixed_graph_is_regular E A r z) : r + 2 * z + 1 ≤ Fintype.card V := by
  inhabit V
  let v : V := default
  have hE_loop : ¬E.Adj v v := E.irrefl
  have hA_loop : ¬A v v := hv.1 v
  have hA_asymm : ∀ x y, A x y → ¬A y x := hv.2.1
  have hEA : ∀ x y, E.Adj x y → ¬A x y := hv.2.2
  obtain ⟨hr1, hr2, hr3⟩ := hr v
  let S0 : Set V := {v}
  let S1 : Set V := {y | E.Adj v y}
  let S2 : Set V := {y | A v y}
  let S3 : Set V := {y | A y v}

  have d01 : Disjoint S0 S1 := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    cases hy1
    exact hE_loop hy2

  have d02 : Disjoint (S0 ∪ S1) S2 := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    rcases hy1 with rfl | hy1
    · exact hA_loop hy2
    · exact hEA v y hy1 hy2

  have d03 : Disjoint (S0 ∪ S1 ∪ S2) S3 := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    rcases hy1 with (rfl | hy1) | hy1
    · exact hA_loop hy2
    · exact hEA y v hy1.symm hy2
    · exact hA_asymm y v hy2 hy1

  have u1 : (S0 ∪ S1).ncard = 1 + r := by
    rw [Set.ncard_union_eq d01, Set.ncard_singleton, hr1]

  have u2 : (S0 ∪ S1 ∪ S2).ncard = 1 + r + z := by
    rw [Set.ncard_union_eq d02, u1, hr2]

  have u3 : (S0 ∪ S1 ∪ S2 ∪ S3).ncard = 1 + r + z + z := by
    rw [Set.ncard_union_eq d03, u2, hr3]

  have h_le : (S0 ∪ S1 ∪ S2 ∪ S3).ncard ≤ Fintype.card V := by
    rw [← Nat.card_eq_fintype_card]
    exact Set.ncard_le_card _

  omega
