import AFTD.Prelude
import AFTD.Kb.Tcs.Op874SixSevenCyclesSeparatedCapacity

/-!
# op874_fourteen_separated_owners_impossible

Topic: combinatorics   Node: 954736da59a9

Provenance: helper lemma. Counting obstruction to separated defect ownership, experiment 35686.

Fourteen distinct owners cannot choose among one external escape and positions on six seven-cycles whose selected positions are separated by at least three.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem op874_fourteen_separated_owners_impossible
    (S : Finset (Fin 6 × Fin 7))
    (hs : ∀ x ∈ S, ∀ y ∈ S, x.1 = y.1 → y.2 ≠ x.2+1 ∧ y.2 ≠ x.2+2)
    (f : Fin 14 → Option (Fin 6 × Fin 7)) (hf : Function.Injective f)
    (hmem : ∀ i x, f i = some x → x ∈ S) : False := by
  classical
  have hc := op874_six_seven_cycles_separated_capacity S hs
  have hsub : (Finset.univ.image f) ⊆ insert none (S.image some) := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    cases he : f i with
    | none => simp
    | some y =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      exact ⟨y, hmem i y he, rfl⟩
  have hsize : (Finset.univ.image f).card = 14 := by
    rw [Finset.card_image_of_injective _ hf]
    decide
  have hupper := Finset.card_le_card hsub
  have hi : (insert none (S.image some)).card ≤ (S.image some).card+1 := Finset.card_insert_le _ _
  have hj : (S.image some).card ≤ S.card := Finset.card_image_le
  omega
