import AFTD.Prelude

/-!
# cycle_seven_diam_eq_three

Topic: graphs   Node: 50ae9337d052

Provenance: helper lemma. folklore; OP-537

The diameter of the 7-cycle graph C_7 is equal to 3.
-/

private def cycle_seven_diam_eq_three_G : SimpleGraph (Fin 7) := SimpleGraph.cycleGraph 7

private lemma cycle_seven_diam_eq_three_adj_add_one (u : Fin 7) :
    cycle_seven_diam_eq_three_G.Adj u (u + 1) := Or.inr (by simp)

private lemma cycle_seven_diam_eq_three_adj_sub_one (u : Fin 7) :
    cycle_seven_diam_eq_three_G.Adj u (u - 1) := Or.inl (by simp)

private lemma cycle_seven_diam_eq_three_edist_add_one_le (u : Fin 7) :
    cycle_seven_diam_eq_three_G.edist u (u + 1) ≤ 1 := by
  rw [SimpleGraph.edist_eq_one_iff_adj.mpr (cycle_seven_diam_eq_three_adj_add_one u)]

private lemma cycle_seven_diam_eq_three_edist_sub_one_le (u : Fin 7) :
    cycle_seven_diam_eq_three_G.edist u (u - 1) ≤ 1 := by
  rw [SimpleGraph.edist_eq_one_iff_adj.mpr (cycle_seven_diam_eq_three_adj_sub_one u)]

private lemma cycle_seven_diam_eq_three_edist_add_two_le (u : Fin 7) :
    cycle_seven_diam_eq_three_G.edist u (u + 2) ≤ 2 := by
  have ht := @SimpleGraph.edist_triangle _ cycle_seven_diam_eq_three_G u (u + 1) (u + 2)
  have h2 : cycle_seven_diam_eq_three_G.edist (u + 1) (u + 2) ≤ 1 := by
    have : u + 2 = (u + 1) + 1 := by rw [add_assoc]; rfl
    rw [this]
    exact cycle_seven_diam_eq_three_edist_add_one_le (u + 1)
  exact le_trans ht (add_le_add (cycle_seven_diam_eq_three_edist_add_one_le u) h2)

private lemma cycle_seven_diam_eq_three_edist_add_three_le (u : Fin 7) :
    cycle_seven_diam_eq_three_G.edist u (u + 3) ≤ 3 := by
  have ht := @SimpleGraph.edist_triangle _ cycle_seven_diam_eq_three_G u (u + 2) (u + 3)
  have h2 : cycle_seven_diam_eq_three_G.edist (u + 2) (u + 3) ≤ 1 := by
    have : u + 3 = (u + 2) + 1 := by rw [add_assoc]; rfl
    rw [this]
    exact cycle_seven_diam_eq_three_edist_add_one_le (u + 2)
  exact le_trans ht (add_le_add (cycle_seven_diam_eq_three_edist_add_two_le u) h2)

private lemma cycle_seven_diam_eq_three_edist_sub_two_le (u : Fin 7) :
    cycle_seven_diam_eq_three_G.edist u (u - 2) ≤ 2 := by
  have ht := @SimpleGraph.edist_triangle _ cycle_seven_diam_eq_three_G u (u - 1) (u - 2)
  have h2 : cycle_seven_diam_eq_three_G.edist (u - 1) (u - 2) ≤ 1 := by
    have : u - 2 = (u - 1) - 1 := by rw [sub_sub]; rfl
    rw [this]
    exact cycle_seven_diam_eq_three_edist_sub_one_le (u - 1)
  exact le_trans ht (add_le_add (cycle_seven_diam_eq_three_edist_sub_one_le u) h2)

private lemma cycle_seven_diam_eq_three_edist_sub_three_le (u : Fin 7) :
    cycle_seven_diam_eq_three_G.edist u (u - 3) ≤ 3 := by
  have ht := @SimpleGraph.edist_triangle _ cycle_seven_diam_eq_three_G u (u - 2) (u - 3)
  have h2 : cycle_seven_diam_eq_three_G.edist (u - 2) (u - 3) ≤ 1 := by
    have : u - 3 = (u - 2) - 1 := by rw [sub_sub]; rfl
    rw [this]
    exact cycle_seven_diam_eq_three_edist_sub_one_le (u - 2)
  exact le_trans ht (add_le_add (cycle_seven_diam_eq_three_edist_sub_two_le u) h2)

private lemma cycle_seven_diam_eq_three_edist_add_four_le (u : Fin 7) (h : 4 < 7) :
    cycle_seven_diam_eq_three_G.edist u (u + ⟨4, h⟩) ≤ 3 := by
  have : u + ⟨4, h⟩ = u - 3 := by ext; simp [Fin.add_def, Fin.sub_def]; omega
  rw [this]
  exact cycle_seven_diam_eq_three_edist_sub_three_le u

private lemma cycle_seven_diam_eq_three_edist_add_five_le (u : Fin 7) (h : 5 < 7) :
    cycle_seven_diam_eq_three_G.edist u (u + ⟨5, h⟩) ≤ 3 := by
  have : u + ⟨5, h⟩ = u - 2 := by ext; simp [Fin.add_def, Fin.sub_def]; omega
  rw [this]
  exact le_trans (cycle_seven_diam_eq_three_edist_sub_two_le u) (by decide)

private lemma cycle_seven_diam_eq_three_edist_add_six_le (u : Fin 7) (h : 6 < 7) :
    cycle_seven_diam_eq_three_G.edist u (u + ⟨6, h⟩) ≤ 3 := by
  have : u + ⟨6, h⟩ = u - 1 := by ext; simp [Fin.add_def, Fin.sub_def]; omega
  rw [this]
  exact le_trans (cycle_seven_diam_eq_three_edist_sub_one_le u) (by decide)

private lemma cycle_seven_diam_eq_three_edist_le_three (u v : Fin 7) :
    cycle_seven_diam_eq_three_G.edist u v ≤ 3 := by
  have h : v = u + (v - u) := by simp
  generalize hd : v - u = d
  rw [hd] at h
  fin_cases d
  · subst h; simp
  · subst h; dsimp only; exact le_trans (cycle_seven_diam_eq_three_edist_add_one_le u) (by decide)
  · subst h; dsimp only; exact le_trans (cycle_seven_diam_eq_three_edist_add_two_le u) (by decide)
  · subst h; dsimp only; exact cycle_seven_diam_eq_three_edist_add_three_le u
  · subst h; dsimp only; exact cycle_seven_diam_eq_three_edist_add_four_le u _
  · subst h; dsimp only; exact cycle_seven_diam_eq_three_edist_add_five_le u _
  · subst h; dsimp only; exact cycle_seven_diam_eq_three_edist_add_six_le u _

/-- The diameter of the 7-cycle graph is 3. -/
theorem cycle_seven_diam_eq_three : (SimpleGraph.cycleGraph 7).diam = 3 := by
  change cycle_seven_diam_eq_three_G.diam = 3
  have h_le : cycle_seven_diam_eq_three_G.ediam ≤ 3 :=
    SimpleGraph.ediam_le_iff.mpr cycle_seven_diam_eq_three_edist_le_three
  have h_prop : (0 : Fin 7) ≠ 3 ∧ ¬ cycle_seven_diam_eq_three_G.Adj 0 3 ∧
      ∀ x, x ∉ cycle_seven_diam_eq_three_G.commonNeighbors 0 3 := by
    dsimp [cycle_seven_diam_eq_three_G]
    decide
  have h_empty : cycle_seven_diam_eq_three_G.commonNeighbors 0 3 = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    exact h_prop.2.2
  have h_lt : 2 < cycle_seven_diam_eq_three_G.edist 0 3 := by
    rw [SimpleGraph.two_lt_edist_iff]
    exact ⟨h_prop.1, h_prop.2.1, h_empty⟩
  have h_ge_edist : 3 ≤ cycle_seven_diam_eq_three_G.edist 0 3 := by
    have h : (2 : ℕ) + 1 ≤ cycle_seven_diam_eq_three_G.edist 0 3 ↔ (2 : ℕ) < cycle_seven_diam_eq_three_G.edist 0 3 :=
      ENat.natCast_add_one_le_iff
    exact h.mpr h_lt
  have h_ge : 3 ≤ cycle_seven_diam_eq_three_G.ediam :=
    le_trans h_ge_edist SimpleGraph.edist_le_ediam
  have h_ediam : cycle_seven_diam_eq_three_G.ediam = 3 := le_antisymm h_le h_ge
  rw [SimpleGraph.diam, h_ediam]
  rfl
