import AFTD.Prelude
import AFTD.Kb.Tcs.IsTernaryLineCover

/-!
# ternary_line_cover_card_ge

Topic: combinatorics   Node: a646563a4a12

Provenance: helper lemma. step towards op_668_ternary_line_cover_first_gap_and_repair

For every natural number n ≥ 1 and every ternary line cover B in (Fin n → ZMod 3), the cardinality of B is at least 3^(n - 1).
-/

/-- Every ternary line cover in dimension n ≥ 1 has cardinality at least 3^(n - 1). -/
theorem ternary_line_cover_card_ge (n : ℕ) (hn : 1 ≤ n) (B : Finset (Fin n → ZMod 3)) (hB : is_ternary_line_cover n B) : 3 ^ (n - 1) ≤ B.card := by
  -- Write n = m + 1 and project along coordinate 0.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let π : (Fin (m + 1) → ZMod 3) → (Fin m → ZMod 3) := fun v j => v (Fin.succ j)
  -- The projection π is surjective when restricted to B.
  have hsurj : ∀ d : Fin m → ZMod 3, ∃ v ∈ B, π v = d := by
    intro d
    obtain ⟨t, ht⟩ := hB 0 (Fin.insertNth (α := fun _ => ZMod 3) 0 0 d)
    refine ⟨Function.update (Fin.insertNth (α := fun _ => ZMod 3) 0 0 d) 0 t, ht, ?_⟩
    funext j
    simp only [π, Function.update_apply, Fin.succ_ne_zero, if_false]
    rfl
  have himage : Finset.image π B = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro d
    obtain ⟨v, hv, hvd⟩ := hsurj d
    exact Finset.mem_image.mpr ⟨v, hv, hvd⟩
  calc 3 ^ m = Fintype.card (Fin m → ZMod 3) := by simp
    _ = (Finset.univ : Finset (Fin m → ZMod 3)).card := (Finset.card_univ).symm
    _ = (Finset.image π B).card := by rw [himage]
    _ ≤ B.card := Finset.card_image_le
