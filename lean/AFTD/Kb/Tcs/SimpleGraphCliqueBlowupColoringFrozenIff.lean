import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCliqueBlowup
import AFTD.Kb.Tcs.SimpleGraphColoringIsFrozen

/-!
# simple_graph_clique_blowup_coloring_frozen_iff

Topic: graphs   Node: a3f0a81f58bc

Provenance: formalization of a published result. Source: arXiv:2610.27527 (Frozen colorings and recolorability of blowups), Lemma 2.1

For a clique blowup G(w) with positive weights, a proper colouring α of G(w) is frozen iff for every colour i the set I_i(α) of vertices v of G whose clique Q_v uses colour i is a maximal independent set of G.
-/

lemma simple_graph_clique_blowup_coloring_frozen_iff_isIndepSet_insert {V : Type*}
    {G : SimpleGraph V} {s : Set V} {v : V}
    (hs : G.IsIndepSet s) (hv : ∀ u ∈ s, ¬G.Adj v u) : G.IsIndepSet (insert v s) := by
  rw [SimpleGraph.isIndepSet_iff] at hs ⊢
  exact hs.insert fun u hu _ => ⟨hv u hu, fun h => hv u hu h.symm⟩

lemma simple_graph_clique_blowup_coloring_frozen_iff_maximal_isIndepSet_iff {V : Type*}
    (G : SimpleGraph V) (s : Set V) :
    Maximal (fun t => G.IsIndepSet t) s ↔ G.IsIndepSet s ∧ ∀ v ∉ s, ∃ u ∈ s, G.Adj v u := by
  constructor
  · rintro ⟨hs, hmax⟩
    refine ⟨hs, fun v hv => ?_⟩
    by_contra! h
    have h_indep : G.IsIndepSet (insert v s) :=
      simple_graph_clique_blowup_coloring_frozen_iff_isIndepSet_insert hs (fun u hu => h u hu)
    have h_sub : s ⊆ insert v s := Set.subset_insert v s
    have h_le : insert v s ⊆ s := hmax h_indep h_sub
    exact hv (h_le (Set.mem_insert v s))
  · rintro ⟨hs, hdom⟩
    refine ⟨hs, fun y hy hsy => ?_⟩
    intro v hv
    by_contra hvs
    obtain ⟨u, hu, hadj⟩ := hdom v hvs
    have hu_y : u ∈ y := hsy hu
    have hne : u ≠ v := by rintro rfl; exact hvs hu
    exact hy hu_y hv hne hadj.symm

lemma simple_graph_clique_blowup_coloring_frozen_iff_indepSet_blowup_color {V : Type*}
    (G : SimpleGraph V) (w : V → ℕ) {k : ℕ}
    (C : (simple_graph_clique_blowup G w).Coloring (Fin k)) (i : Fin k) :
    G.IsIndepSet {v | ∃ a : Fin (w v), C ⟨v, a⟩ = i} := by
  intro u hu v hv hne
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  intro hadj
  have hadj_blowup : (simple_graph_clique_blowup G w).Adj ⟨u, a⟩ ⟨v, b⟩ := Or.inr hadj
  have h_ne_col := C.valid hadj_blowup
  rw [ha, hb] at h_ne_col
  exact h_ne_col rfl

theorem simple_graph_clique_blowup_coloring_frozen_iff {V : Type*} (G : SimpleGraph V)
    (w : V → ℕ) (hw : ∀ v, 0 < w v) {k : ℕ} (C : (simple_graph_clique_blowup G w).Coloring (Fin k)) :
    simple_graph_coloring_is_frozen C ↔
      ∀ i : Fin k, Maximal (fun s : Set V => G.IsIndepSet s) {v | ∃ a : Fin (w v), C ⟨v, a⟩ = i} := by
  constructor
  · intro h_frozen i
    rw [simple_graph_clique_blowup_coloring_frozen_iff_maximal_isIndepSet_iff]
    refine ⟨simple_graph_clique_blowup_coloring_frozen_iff_indepSet_blowup_color G w C i, fun v hv => ?_⟩
    have h0 : 0 < w v := hw v
    have h_froz := h_frozen ⟨v, ⟨0, h0⟩⟩ i
    rcases h_froz with h_same | ⟨y, hadj, hy_col⟩
    · exfalso
      exact hv ⟨⟨0, h0⟩, h_same⟩
    · rcases hadj with ⟨h1, h2⟩ | hadj_G
      · exfalso
        obtain ⟨u, b⟩ := y
        dsimp at h1
        subst h1
        exact hv ⟨b, hy_col⟩
      · obtain ⟨u, b⟩ := y
        exact ⟨u, ⟨b, hy_col⟩, hadj_G⟩
  · intro h_max x i
    obtain ⟨v, a⟩ := x
    by_cases hv : ∃ b : Fin (w v), C ⟨v, b⟩ = i
    · obtain ⟨b, hb⟩ := hv
      by_cases hab : a = b
      · subst hab
        exact Or.inl hb
      · right
        refine ⟨⟨v, b⟩, ?_, hb⟩
        left
        refine ⟨rfl, ?_⟩
        intro h_eq
        cases h_eq
        exact hab rfl
    · right
      have h_max_i := (simple_graph_clique_blowup_coloring_frozen_iff_maximal_isIndepSet_iff G {v | ∃ a : Fin (w v), C ⟨v, a⟩ = i}).mp (h_max i)
      obtain ⟨u, ⟨b, hb⟩, hadj⟩ := h_max_i.2 v hv
      refine ⟨⟨u, b⟩, Or.inr hadj, hb⟩
