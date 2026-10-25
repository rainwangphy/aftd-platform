import AFTD.Prelude

/-!
# complete_graph_line_graph_colorable

Topic: graphs   Node: 3231d81a6e66

Provenance: helper lemma. step towards complete_graph_odd_line_graph_chromatic_number_eq

The line graph of K_n is n-colorable for n ≥ 3.
-/

/-- The line graph of K_n is n-colorable for n ≥ 3. -/
theorem complete_graph_line_graph_colorable (n : ℕ) (hn : 3 ≤ n) : (⊤ : SimpleGraph (Fin n)).lineGraph.Colorable n := by
  let col : Sym2 (Fin n) → Fin n := Sym2.lift ⟨fun a b => (⟨(a.val + b.val) % n, Nat.mod_lt _ (by omega)⟩ : Fin n),
    fun a b => by simp [Nat.add_comm]⟩
  refine ⟨SimpleGraph.Coloring.mk (fun e => col e.val) ?_⟩
  intro e₁ e₂ h
  rw [SimpleGraph.lineGraph_adj_iff_exists] at h
  obtain ⟨hne, v, h1, h2⟩ := h
  obtain ⟨a, ha⟩ : ∃ a, (e₁ : Sym2 (Fin n)) = s(v, a) := (Sym2.mem_iff_exists.mp h1).imp fun a h => h
  obtain ⟨b, hb⟩ : ∃ b, (e₂ : Sym2 (Fin n)) = s(v, b) := (Sym2.mem_iff_exists.mp h2).imp fun a h => h
  intro hc
  apply hne
  apply Subtype.ext
  rw [ha, hb]
  simp only [col, ha, hb, Sym2.lift_mk, Fin.mk.injEq] at hc
  have h3 := Nat.ModEq.add_left_cancel' v.val hc
  have : a.val = b.val := Nat.ModEq.eq_of_lt_of_lt h3 a.isLt b.isLt
  rw [Fin.ext this]
