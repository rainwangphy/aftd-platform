import AFTD.Prelude

/-!
# op309_girth5_five_clique_palette_obstruction

Topic: graphs   Node: 858cc2a1bed6

Provenance: helper lemma. OP-309; girth-five fixed-P3 obstruction, experiments 41671, 41673, 41674, 41678 and 41684.

The stated finite five-color domain constraints are inconsistent.
-/

theorem op309_girth5_five_clique_palette_obstruction
    (a0 a1 a2 a3 a4 b2 b7 b8 b10 b11 b12 b13 b14 b15 b16 : Fin 5)
    (hclique : ([a0,a1,a2,a3,a4] : List (Fin 5)).Nodup)
    (h14 : b14 ≠ a1 ∧ b14 ≠ a2 ∧ b14 ≠ a3 ∧ b14 ≠ a4)
    (h16 : b16 ≠ a1 ∧ b16 ≠ a3 ∧ b16 ≠ a4 ∧ b16 ≠ b14)
    (h2 : b2 ≠ a3 ∧ b2 ≠ b14 ∧ b2 ≠ b16)
    (h12 : b12 ≠ a2 ∧ b12 ≠ b14 ∧ b12 ≠ b2)
    (h13 : b13 ≠ a2 ∧ b13 ≠ b14 ∧ b13 ≠ b2 ∧ b13 ≠ b12)
    (h7 : b7 ≠ a0 ∧ b7 ≠ b2 ∧ b7 ≠ b12 ∧ b7 ≠ b13)
    (h10 : b10 ≠ a2 ∧ b10 ≠ b14 ∧ b10 ≠ b12 ∧ b10 ≠ b13)
    (h15 : b15 ≠ a0 ∧ b15 ≠ b2 ∧ b15 ≠ b7)
    (h8 : b8 ≠ a0 ∧ b8 ≠ b7 ∧ b8 ≠ b10 ∧ b8 ≠ b15)
    (h11 : b11 ≠ a0 ∧ b11 ≠ b7 ∧ b11 ≠ b10 ∧ b11 ≠ b15 ∧ b11 ≠ b8) : False := by
  set_option maxHeartbeats 4000000 in
    classical
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
      List.nodup_singleton, not_or] at hclique
    let f : Fin 5 → Fin 5 := ![a0,a1,a2,a3,a4]
    have hf : Function.Injective f := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [f]
    have cover (x : Fin 5) : x=a0 ∨ x=a1 ∨ x=a2 ∨ x=a3 ∨ x=a4 := by
      obtain ⟨i,hi⟩ := (Finite.surjective_of_injective hf) x
      fin_cases i <;> simp_all [f]
    rcases cover b14 with h | h | h | h | h <;> simp_all
    rcases cover b16 with h | h | h | h | h <;> simp_all
    rcases cover b2 with h | h | h | h | h <;> simp_all
    all_goals rcases cover b12 with h | h | h | h | h <;> simp_all
    all_goals rcases cover b13 with h | h | h | h | h <;> simp_all
    all_goals rcases cover b7 with h | h | h | h | h <;> simp_all
    all_goals rcases cover b10 with h | h | h | h | h <;> simp_all
    all_goals rcases cover b15 with h | h | h | h | h <;> simp_all
    all_goals rcases cover b8 with h | h | h | h | h <;> simp_all
    all_goals rcases cover b11 with h | h | h | h | h <;> simp_all
