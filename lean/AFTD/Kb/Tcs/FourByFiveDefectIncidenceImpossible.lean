import AFTD.Prelude

/-!
# four_by_five_defect_incidence_impossible

Topic: graphs   Node: 3eaebdaabf22

Provenance: helper lemma. OP-1957: degree and incidence bounds for the size-five block route.

A relation between sets of sizes four and five cannot give each of the five vertices at least two neighbors while giving each of the four vertices at most two neighbors.
-/

theorem four_by_five_defect_incidence_impossible
    {V : Type*} [DecidableEq V] (A C : Finset V) (R : V → V → Prop) [DecidableRel R]
    (hA : A.card = 4) (hC : C.card = 5)
    (hupper : ∀ a ∈ A, (C.filter (R a)).card ≤ 2)
    (hlower : ∀ c ∈ C, 2 ≤ (A.filter (fun a => R a c)).card) : False := by
  classical
  have hl : (∑ c ∈ C, (2 : ℕ)) ≤ ∑ c ∈ C, (A.filter (fun a => R a c)).card :=
    Finset.sum_le_sum hlower
  have hu : (∑ a ∈ A, (C.filter (R a)).card) ≤ ∑ a ∈ A, (2 : ℕ) :=
    Finset.sum_le_sum hupper
  have hl' : 10 ≤ ∑ c ∈ C, (A.filter (fun a => R a c)).card := by
    simpa [hC] using hl
  have hu' : (∑ a ∈ A, (C.filter (R a)).card) ≤ 8 := by
    simpa [hA] using hu
  have heq : (∑ c ∈ C, (A.filter (fun a => R a c)).card) =
      ∑ a ∈ A, (C.filter (R a)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  omega
