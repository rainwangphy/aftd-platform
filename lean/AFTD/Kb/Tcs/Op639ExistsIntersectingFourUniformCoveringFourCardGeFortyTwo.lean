import AFTD.Prelude

/-!
# op_639_exists_intersecting_four_uniform_covering_four_card_ge_forty_two

Topic: combinatorics   Node: 13da879c9930

Provenance: formalization of a published result. Source: arXiv:2610.37315, Section 1, citing Frankl-Ota-Tokushige (1996)

There exists an intersecting 4-uniform hypergraph on the natural numbers with covering number 4 having at least 42 edges.
-/

def op_639_fot_edges : List (Finset ℕ) := Id.run do
  let V1 : List ℕ := [0, 1]
  let V2 : List ℕ := [2, 3]
  let V4 : List ℕ := [7, 8, 9]
  let p3 := [[4, 5], [4, 6], [5, 6]]
  let mut res : List (Finset ℕ) := []
  res := ({0, 1, 2, 3} : Finset ℕ) :: res
  for x1 in V1 do
    for p in p3 do
      for x4 in V4 do
        res := {x1, p[0]!, p[1]!, x4} :: res
  for p in p3 do
    res := {2, 3, p[0]!, p[1]!} :: res
  for x2 in V2 do
    for p in p3 do
      for x4 in V4 do
        res := {x2, p[0]!, p[1]!, x4} :: res
  for x2 in V2 do
    res := {x2, 7, 8, 9} :: res
  return res

def op_639_fot_F : Finset (Finset ℕ) := op_639_fot_edges.toFinset

def op_639_fot_V : Finset ℕ := Finset.range 10

lemma op_639_disjoint_of_disjoint_inter {α : Type*} [DecidableEq α] {e T V : Finset α}
    (he : e ⊆ V) (hd : Disjoint e (T ∩ V)) : Disjoint e T := by
  rw [Finset.disjoint_right] at hd ⊢
  intro x hx hxe
  exact hd (Finset.mem_inter.mpr ⟨hx, he hxe⟩) hxe

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

lemma op_639_fot_edges_sub_V : ∀ e ∈ op_639_fot_F, e ⊆ op_639_fot_V := by decide

lemma op_639_fot_tau_finite : ∀ T ∈ op_639_fot_V.powerset, T.card < 4 → ∃ e ∈ op_639_fot_F, Disjoint e T := by decide

/-- Frankl, Ota, and Tokushige (1996) proved m(4) >= 42 by constructing an intersecting 4-uniform hypergraph with covering number 4 of size 42. -/
theorem op_639_exists_intersecting_four_uniform_covering_four_card_ge_forty_two :
    ∃ (F : Finset (Finset ℕ)),
      (∀ e ∈ F, e.card = 4) ∧
      (F : Set (Finset ℕ)).Intersecting ∧
      (∀ T : Finset ℕ, T.card < 4 → ∃ e ∈ F, Disjoint e T) ∧
      42 ≤ F.card := by
  use op_639_fot_F
  refine ⟨by decide, ?_, ?_, by decide⟩
  · intro a ha b hb
    rw [Finset.mem_coe] at ha hb
    revert a ha b hb
    decide
  · intro T hT
    have hT' : (T ∩ op_639_fot_V).card < 4 := lt_of_le_of_lt (Finset.card_le_card Finset.inter_subset_left) hT
    obtain ⟨e, heF, hd⟩ := op_639_fot_tau_finite (T ∩ op_639_fot_V) (Finset.mem_powerset.mpr Finset.inter_subset_right) hT'
    exact ⟨e, heF, op_639_disjoint_of_disjoint_inter (op_639_fot_edges_sub_V e heF) hd⟩
