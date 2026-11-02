import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeTokenK2nLeftCount

/-!
# three_token_k2n_left_count_le_two

Topic: graphs   Node: 8b08e3fcec00

Provenance: helper lemma. Explicit construction for three_token_k2n_has_dominating_set and OP-666.

Every three-token configuration over Fin 2 plus Fin n contains at most two vertices from the left part.
-/

theorem three_token_k2n_left_count_le_two {n : ℕ}
    (z : {s : Finset (Fin 2 ⊕ Fin n) // s.card = 3}) : three_token_k2n_left_count z ≤ 2 := by
  classical
  unfold three_token_k2n_left_count
  have hs : z.val.filter (fun v => ∃ i : Fin 2, v = Sum.inl i) ⊆
      Finset.univ.image (Sum.inl : Fin 2 → Fin 2 ⊕ Fin n) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at *
    obtain ⟨_, i, rfl⟩ := hx
    exact ⟨i, rfl⟩
  calc
    _ ≤ (Finset.univ.image (Sum.inl : Fin 2 → Fin 2 ⊕ Fin n)).card := Finset.card_le_card hs
    _ ≤ (Finset.univ : Finset (Fin 2)).card := Finset.card_image_le
    _ = 2 := by simp
