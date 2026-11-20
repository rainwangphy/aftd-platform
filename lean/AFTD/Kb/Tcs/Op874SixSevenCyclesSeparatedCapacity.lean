import AFTD.Prelude
import AFTD.Kb.Tcs.Op874SevenCycleSeparatedCapacity

/-!
# op874_six_seven_cycles_separated_capacity

Topic: combinatorics   Node: 7da84ab61365

Provenance: helper lemma. Separated ownership capacity obstruction, experiment 35686.

Six seven-cycles together contain at most twelve selected vertices when selected vertices on each cycle are separated by at least three.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem op874_six_seven_cycles_separated_capacity (S : Finset (Fin 6 × Fin 7))
    (hs : ∀ x ∈ S, ∀ y ∈ S, x.1 = y.1 → y.2 ≠ x.2+1 ∧ y.2 ≠ x.2+2) :
    S.card ≤ 12 := by
  classical
  let F : Fin 6 → Finset (Fin 7) := fun i => Finset.univ.filter (fun j => (i,j) ∈ S)
  have hF (i : Fin 6) : (F i).card ≤ 2 := by
    apply op874_seven_cycle_separated_capacity
    intro j hj
    have hmem : (i,j) ∈ S := by simpa [F] using hj
    have h1 : (i,j+1) ∉ S := by
      intro hh
      have h := hs (i,j) hmem (i,j+1) hh rfl
      exact h.1 rfl
    have h2 : (i,j+2) ∉ S := by
      intro hh
      have h := hs (i,j) hmem (i,j+2) hh rfl
      exact h.2 rfl
    simp [F, h1, h2]
  have hcover : S ⊆ Finset.univ.biUnion (fun i : Fin 6 => (F i).image (fun j => (i,j))) := by
    intro x hx
    apply Finset.mem_biUnion.mpr
    refine ⟨x.1, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨x.2, by simpa [F] using hx, Prod.mk.eta⟩
  calc
    S.card ≤ (Finset.univ.biUnion (fun i : Fin 6 => (F i).image (fun j => (i,j)))).card := Finset.card_le_card hcover
    _ ≤ ∑ i : Fin 6, ((F i).image (fun j => (i,j))).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 6, 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.card_image_le).trans (hF i)
    _ = 12 := by decide
