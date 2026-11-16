import AFTD.Prelude

/-!
# op1370_coordinate_fiber_defect_identity

Topic: combinatorics   Node: 42094df17eab

Provenance: helper lemma. Coordinate-fiber counting helper for OP-1370, arXiv:2611.12199 Conjecture 4.3.

For a family U of subsets of Fin n and a coordinate x, the size of U plus the number of missing x-erased fibers equals 2^(n-1) plus the number of doubled x-erased fibers.
-/

theorem op1370_coordinate_fiber_defect_identity (n : ℕ) (x : Fin n) (U : Finset (Finset (Fin n))) : let V := Finset.univ.erase x; let P := U.filter (fun S => x ∉ S); let Q := (U.filter (fun S => x ∈ S)).image (fun S => S.erase x); U.card + (V.powerset \ (P ∪ Q)).card = 2 ^ (n - 1) + (P ∩ Q).card := by
  open Finset in
  classical
  dsimp only
  let V : Finset (Fin n) := univ.erase x
  let P := U.filter (fun S => x ∉ S)
  let Q0 := U.filter (fun S => x ∈ S)
  let Q := Q0.image (fun S => S.erase x)
  change U.card + (V.powerset \ (P ∪ Q)).card = 2 ^ (n - 1) + (P ∩ Q).card
  have hsub : P ∪ Q ⊆ V.powerset := by
    intro S hS
    rw [mem_powerset]
    intro z hz
    simp only [V, mem_erase, mem_univ, and_true]
    intro hzx
    subst z
    rcases mem_union.mp hS with hP | hQ
    · exact (mem_filter.mp hP).2 hz
    · obtain ⟨T, _, rfl⟩ := mem_image.mp hQ
      exact (mem_erase.mp hz).1 rfl
  have hQcard : Q.card = Q0.card := by
    apply card_image_of_injOn
    intro a ha b hb hab
    have hax : x ∈ a := (mem_filter.mp ha).2
    have hbx : x ∈ b := (mem_filter.mp hb).2
    change a.erase x = b.erase x at hab
    calc
      a = insert x (a.erase x) := (insert_erase hax).symm
      _ = insert x (b.erase x) := by rw [hab]
      _ = b := insert_erase hbx
  have hsplit : P.card + Q0.card = U.card := by
    simpa [P, Q0, Nat.add_comm] using
      (card_filter_add_card_filter_not (s := U) (fun s => x ∈ s))
  have hVcard : V.card = n - 1 := by simp [V]
  have hpow : V.powerset.card = 2 ^ (n - 1) := by simp [hVcard]
  have hdiff := card_sdiff_of_subset hsub
  rw [hpow] at hdiff
  have hle := card_le_card hsub
  rw [hpow] at hle
  have hinclex := card_union_add_card_inter P Q
  omega
