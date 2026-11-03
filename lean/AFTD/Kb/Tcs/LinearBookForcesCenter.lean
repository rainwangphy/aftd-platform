import AFTD.Prelude

/-!
# linear_book_forces_center

Topic: graphs   Node: fb4991c9b445

Provenance: helper lemma. Related sunflower and triangle-kernel reductions: https://link.springer.com/article/10.1007/s00453-022-00986-0 and https://arxiv.org/abs/2308.16515. This is a structural helper for the triangle packing-cover campaign, with no claim of novelty.

In a finite linear family of sets all containing a fixed point, every transversal smaller than the family contains that point.
-/

open Finset
set_option maxHeartbeats 1000000

theorem linear_book_forces_center {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (b : α) (C : Finset α)
    (hb : ∀ A ∈ H, b ∈ A)
    (hl : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (hh : ∀ A ∈ H, ¬Disjoint A C)
    (hc : C.card < H.card) : b ∈ C := by
  classical
  by_contra hn
  let f (A : Finset α) : α :=
    if hA : A ∈ H then Classical.choose (Finset.not_disjoint_iff.mp (hh A hA)) else b
  have hf : ∀ A ∈ H, f A ∈ A ∧ f A ∈ C := by
    intro A hA
    simpa [f, hA] using Classical.choose_spec (Finset.not_disjoint_iff.mp (hh A hA))
  have hcard : H.card ≤ C.card := by
    apply Finset.card_le_card_of_injOn f
    · intro A hA
      exact (hf A hA).2
    · intro A hA B hB hab
      by_contra hne
      have hu : ∀ {a b : α}, a ∈ A ∩ B → b ∈ A ∩ B → a = b := Finset.card_le_one_iff.mp (hl A hA B hB hne)
      have hbi : b ∈ A ∩ B := Finset.mem_inter.mpr ⟨hb A hA, hb B hB⟩
      have hfi : f A ∈ A ∩ B := Finset.mem_inter.mpr ⟨(hf A hA).1, by rw [hab]; exact (hf B hB).1⟩
      have heq : b = f A := hu hbi hfi
      apply hn
      rw [heq]
      exact (hf A hA).2
  omega
