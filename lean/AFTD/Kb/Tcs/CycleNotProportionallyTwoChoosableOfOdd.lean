import AFTD.Prelude

/-!
# cycle_not_proportionally_two_choosable_of_odd

Topic: graphs   Node: 4fbeef16db67

Provenance: helper lemma. step towards cycle_not_proportionally_two_choosable

For every odd integer n ≥ 3, the simple n-cycle C_n is not proportionally 2-choosable.
-/

/-- Odd cycles C_n (n ≥ 3) are not proportionally 2-choosable (they are not even 2-colorable). -/
theorem cycle_not_proportionally_two_choosable_of_odd (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] (L : Fin n → Finset α),
      (∀ v, (L v).card = 2) →
      ∃ f : (SimpleGraph.cycleGraph n).Coloring α,
        (∀ v, f v ∈ L v) ∧
        ∀ c : α,
          let η := (Finset.univ.filter (fun v => c ∈ L v)).card
          let uses := (Finset.univ.filter (fun v => f v = c)).card
          uses = η / 2 ∨ uses = η ⌈/⌉ 2 := by
  intro H
  -- Use the palette `Fin 2` and give every vertex the full list.
  have hcol : (SimpleGraph.cycleGraph n).Colorable 2 := by
    obtain ⟨f, -, -⟩ := H (Fin 2) (fun _ => Finset.univ) (by simp)
    exact ⟨f⟩
  -- A 2-coloring would force the chromatic number to be at most 2,
  -- but an odd cycle has chromatic number 3.
  have hle := SimpleGraph.Colorable.chromaticNumber_le hcol
  have hchrom := SimpleGraph.chromaticNumber_cycleGraph_of_odd n (by omega) hodd
  rw [hchrom] at hle
  norm_num at hle
