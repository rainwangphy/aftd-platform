import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsTreeSumChooseDegreeEqIffStar
import AFTD.Kb.Tcs.SimpleGraphIsTreeSumChooseDegreeEqIffPath
import AFTD.Kb.Tcs.SimpleGraphIsTreeCardSubTwoLeSumChooseDegreeLeChoose
import AFTD.Kb.Tcs.G

/-!
# op223_tree_fin_four_iso_path_or_star

Topic: graphs   Node: b970b2d3f5d4

Provenance: helper lemma. step towards op223_sustainable_tree_fin_four

Every tree on four vertices is isomorphic either to the path graph on four vertices or to the star K_{1,3}.
-/

noncomputable def op223_tree_fin_four_iso_path_or_star_equiv (r : Fin 4) : Fin 4 ≃ Fin 1 ⊕ Fin 3 :=
  let e₀ : Fin 4 ≃ Fin 1 ⊕ Fin 3 := Fintype.equivOfCardEq (by decide)
  e₀.trans (Equiv.swap (e₀ r) (Sum.inl 0))

theorem op223_tree_fin_four_iso_path_or_star_equiv_apply_center (r : Fin 4) :
    op223_tree_fin_four_iso_path_or_star_equiv r r = Sum.inl 0 := by
  dsimp [op223_tree_fin_four_iso_path_or_star_equiv]
  exact Equiv.swap_apply_left _ _

noncomputable def op223_tree_fin_four_iso_path_or_star_starIso (r : Fin 4) :
    SimpleGraph.starGraph r ≃g completeBipartiteGraph (Fin 1) (Fin 3) where
  toEquiv := op223_tree_fin_four_iso_path_or_star_equiv r
  map_rel_iff' {x y} := by
    rw [SimpleGraph.starGraph_adj, completeBipartiteGraph_adj]
    have hx : op223_tree_fin_four_iso_path_or_star_equiv r x = Sum.inl 0 ↔ x = r := by
      rw [← op223_tree_fin_four_iso_path_or_star_equiv_apply_center r]
      exact (op223_tree_fin_four_iso_path_or_star_equiv r).injective.eq_iff
    have hy : op223_tree_fin_four_iso_path_or_star_equiv r y = Sum.inl 0 ↔ y = r := by
      rw [← op223_tree_fin_four_iso_path_or_star_equiv_apply_center r]
      exact (op223_tree_fin_four_iso_path_or_star_equiv r).injective.eq_iff
    have h_left (z : Fin 1 ⊕ Fin 3) : z.isLeft = true ↔ z = Sum.inl 0 := by
      cases z with
      | inl a =>
        fin_cases a
        simp
      | inr b => simp
    have h_right (z : Fin 1 ⊕ Fin 3) : z.isRight = true ↔ z ≠ Sum.inl 0 := by
      cases z with
      | inl a =>
        fin_cases a
        simp
      | inr b => simp
    rw [h_left, h_right, h_left, h_right]
    have hx_ne : op223_tree_fin_four_iso_path_or_star_equiv r x ≠ Sum.inl 0 ↔ x ≠ r := not_iff_not.2 hx
    have hy_ne : op223_tree_fin_four_iso_path_or_star_equiv r y ≠ Sum.inl 0 ↔ y ≠ r := not_iff_not.2 hy
    rw [hx, hy, hx_ne, hy_ne]
    constructor
    · rintro (⟨rfl, hy⟩ | ⟨hx, rfl⟩)
      · exact ⟨fun h => hy (h ▸ rfl), Or.inl rfl⟩
      · exact ⟨fun h => hx (h ▸ rfl), Or.inr rfl⟩
    · rintro ⟨hxy, rfl | rfl⟩
      · exact Or.inl ⟨rfl, hxy.symm⟩
      · exact Or.inr ⟨hxy, rfl⟩

/-- The only trees on four vertices are the path P4 and the star K_{1,3}. -/
theorem op223_tree_fin_four_iso_path_or_star (X : SimpleGraph (Fin 4)) (hX : X.IsTree) :
    Nonempty (X ≃g SimpleGraph.pathGraph 4) ∨
      Nonempty (X ≃g completeBipartiteGraph (Fin 1) (Fin 3)) := by
  classical
  have hk : 2 ≤ Fintype.card (Fin 4) := by decide
  have hbounds := simple_graph_is_tree_card_sub_two_le_sum_choose_degree_le_choose X hX hk
  have hcard : Fintype.card (Fin 4) = 4 := rfl
  have hchoose : (4 - 1).choose 2 = 3 := by decide
  rw [hcard] at hbounds
  have h_le : 2 ≤ ∑ v, (X.degree v).choose 2 ∧ ∑ v, (X.degree v).choose 2 ≤ 3 := by
    omega
  rcases eq_or_lt_of_le h_le.2 with h3 | hlt
  · -- sum is 3: star
    right
    have hsum : ∑ v, (X.degree v).choose 2 = (Fintype.card (Fin 4) - 1).choose 2 := by
      rw [hcard, hchoose]
      exact h3
    rw [simple_graph_is_tree_sum_choose_degree_eq_iff_star X hX hk] at hsum
    obtain ⟨r, rfl⟩ := hsum
    exact ⟨op223_tree_fin_four_iso_path_or_star_starIso r⟩
  · -- sum is 2: path
    left
    have h2 : ∑ v, (X.degree v).choose 2 = 2 := by omega
    have hsum : ∑ v, (X.degree v).choose 2 = Fintype.card (Fin 4) - 2 := by
      rw [hcard]
      exact h2
    rw [simple_graph_is_tree_sum_choose_degree_eq_iff_path X hX hk] at hsum
    rw [hcard] at hsum
    exact hsum
