import AFTD.Prelude

/-!
# op_258_pigeonhole_blocks

Topic: combinatorics   Node: dc61ffbb30d0

Provenance: helper lemma. step towards op_258_forces_of_forces_smul_blowup

Let s be a finite set and f : α → Fin γ. If γ * k ≤ |s| and γ ≥ 1, then there exists b ∈ Fin γ with |{x ∈ s | f x = b}| ≥ k.
-/

/-- Pigeonhole principle on finsets partitioned into γ classes: if s has cardinality at least γ * k, then some fiber under f : α → Fin γ has cardinality at least k. -/
theorem op_258_pigeonhole_blocks {α : Type*} (s : Finset α)
    (γ k : ℕ) (hγ : 1 ≤ γ) (f : α → Fin γ) (hs : γ * k ≤ s.card) :
    ∃ b : Fin γ, k ≤ (s.filter (fun x => f x = b)).card := by
  have ht : (Finset.univ : Finset (Fin γ)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_fin]
    omega
  have hmul : (Finset.univ : Finset (Fin γ)).card * k ≤ s.card := by
    rw [Finset.card_fin]
    exact hs
  obtain ⟨b, -, hb⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (fun a _ => Finset.mem_univ (f a)) ht hmul
  exact ⟨b, hb⟩
