import AFTD.Prelude
import AFTD.Kb.Tcs.HasMadLt

/-!
# has_mad_lt_exists_degree_le_two

Topic: graphs   Node: b4f9d0131189

Provenance: helper lemma. step towards sparse_strong_odd_five_list_coloring

If has_mad_lt G (7/3) holds, then every nonempty finite vertex set s contains a vertex with at most 2 neighbours in s.
-/

/-- `mad < 7/3` forces 2-degeneracy: every nonempty vertex set contains a vertex with at most 2 neighbours inside it. -/
theorem has_mad_lt_exists_degree_le_two {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hmad : has_mad_lt G (7 / 3)) :
    ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, {w ∈ s | G.Adj v w}.card ≤ 2 := by
  intro s hs
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hm := hmad s hs
  set H := G.induce (s : Set V) with hH
  have hdeg : ∀ x : (s : Set V), 3 ≤ H.degree x := by
    intro x
    have hx := hcon x.1 x.2
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : ({w ∈ s | G.Adj x.1 w}) = (H.neighborFinset x).map (Function.Embedding.subtype _) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_map, SimpleGraph.mem_neighborFinset,
        Function.Embedding.coe_subtype, hH, SimpleGraph.comap_adj, SimpleGraph.induce,
        Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨hw, hadj⟩
        exact ⟨⟨w, hw⟩, hadj, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
    rw [this, Finset.card_map] at hx
    omega
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges H
  have hle : ∑ _x : (s : Set V), (3 : ℕ) ≤ ∑ x : (s : Set V), H.degree x :=
    Finset.sum_le_sum fun x _ => hdeg x
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
  have hcard : Fintype.card (s : Set V) = s.card := by simp
  rw [hcard] at hle
  have hspos : (0 : ℚ) < s.card := by exact_mod_cast hs.card_pos
  rw [div_lt_iff₀ hspos] at hm
  have h2 : (3 * s.card : ℚ) ≤ 2 * (H.edgeFinset.card : ℚ) := by
    have : s.card * 3 ≤ 2 * H.edgeFinset.card := by
      have := hsum ▸ hle
      convert this using 2
    exact_mod_cast (by omega : 3 * s.card ≤ 2 * H.edgeFinset.card)
  have : (2 * (H.edgeFinset.card : ℚ)) = 2 * ((G.induce (s : Set V)).edgeFinset.card : ℚ) := by
    congr 2
  linarith
