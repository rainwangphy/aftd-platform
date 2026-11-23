import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# is_k_rollercoaster

Topic: algorithms   Node: d3fbf79a83be

Provenance: formalization of a published result. Source: arXiv:2611.26297 Sec. 1

A list L of distinct elements from a linearly ordered set is a k-rollercoaster if its length is at least k, every turning point is at least k - 1 indices away from both ends, and any two turning points are separated by at least k - 1 indices.
-/

/-- A k-rollercoaster is a sequence of distinct elements whose maximal increasing and decreasing runs all have length at least k. -/
def is_k_rollercoaster {α : Type*} [LinearOrder α] (k : ℕ) (L : List α) : Prop :=
  L.Nodup ∧
  k ≤ L.length ∧
  (∀ i, (∃ (h0 : 0 < i) (h1 : i + 1 < L.length),
    (L.get ⟨i - 1, by omega⟩ < L.get ⟨i, by omega⟩ ∧ L.get ⟨i + 1, h1⟩ < L.get ⟨i, by omega⟩) ∨
    (L.get ⟨i, by omega⟩ < L.get ⟨i - 1, by omega⟩ ∧ L.get ⟨i, by omega⟩ < L.get ⟨i + 1, h1⟩)) →
    k - 1 ≤ i ∧ i + (k - 1) < L.length) ∧
  (∀ i j, (∃ (h0 : 0 < i) (h1 : i + 1 < L.length),
    (L.get ⟨i - 1, by omega⟩ < L.get ⟨i, by omega⟩ ∧ L.get ⟨i + 1, h1⟩ < L.get ⟨i, by omega⟩) ∨
    (L.get ⟨i, by omega⟩ < L.get ⟨i - 1, by omega⟩ ∧ L.get ⟨i, by omega⟩ < L.get ⟨i + 1, h1⟩)) →
    (∃ (h0 : 0 < j) (h1 : j + 1 < L.length),
    (L.get ⟨j - 1, by omega⟩ < L.get ⟨j, by omega⟩ ∧ L.get ⟨j + 1, h1⟩ < L.get ⟨j, by omega⟩) ∨
    (L.get ⟨j, by omega⟩ < L.get ⟨j - 1, by omega⟩ ∧ L.get ⟨j, by omega⟩ < L.get ⟨j + 1, h1⟩)) →
    i < j → k - 1 ≤ j - i)
