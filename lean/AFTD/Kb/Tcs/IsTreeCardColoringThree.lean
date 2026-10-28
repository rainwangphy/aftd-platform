import AFTD.Prelude
import AFTD.Kb.Tcs.IsTreeInduceComplSingleton
import AFTD.Kb.Tcs.IsTreeCardColoringThreeSubsingleton
import AFTD.Kb.Tcs.IsTreeCardColoringThreeLeaf

/-!
# is_tree_card_coloring_three

Topic: graphs   Node: a7a91c03b0f3

Provenance: helper lemma. step towards caterpillar_third_t_chromatic_specialization_fiber_le_two

For every finite tree T, the number of proper 3-colorings of T is 3 * 2^(|V| - 1).
-/

private lemma is_tree_card_coloring_three_aux.{u} :
    ∀ (n : Nat) (V : Type u) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
      Fintype.card V = n → T.IsTree →
      Fintype.card (T.Coloring (Fin 3)) = 3 * 2 ^ (n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ T _ hcard hT
    cases n with
    | zero =>
        exfalso
        have hne : Nonempty V := hT.connected.nonempty
        have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hne
        omega
    | succ m =>
        cases m with
        | zero =>
            haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
            haveI : Nonempty V := hT.connected.nonempty
            rw [is_tree_card_coloring_three_subsingleton T]
            simp
        | succ k =>
            haveI : Nontrivial V := by
              rw [nontrivial_iff]
              exact Fintype.one_lt_card_iff.mp (by omega)
            obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
            rw [is_tree_card_coloring_three_leaf T hv]
            have hT' : (T.induce (({v} : Set V)ᶜ)).IsTree :=
              is_tree_induce_compl_singleton T hT hv
            have hcard' : Fintype.card ↥(({v} : Set V)ᶜ) = k + 1 := by
              have h1 : Fintype.card ↥(({v} : Set V)ᶜ) =
                  Fintype.card V - Fintype.card {x : V // x ∈ ({v} : Set V)} := by
                show Fintype.card {x : V // ¬ x ∈ ({v} : Set V)} = _
                exact Fintype.card_subtype_compl (fun x : V => x ∈ ({v} : Set V))
              rw [h1]
              simp
              omega
            have hih := ih (k + 1) (by omega) ↥(({v} : Set V)ᶜ)
              (T.induce (({v} : Set V)ᶜ)) hcard' hT'
            rw [hih]
            have e : k + 1 - 1 = k := by omega
            rw [e]
            have e2 : k + 1 + 1 - 1 = k + 1 := by omega
            rw [e2]
            ring

/-- For every finite tree T, the number of proper 3-colorings is 3 * 2^(|V| - 1). -/
theorem is_tree_card_coloring_three {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) :
    Fintype.card (T.Coloring (Fin 3)) = 3 * 2 ^ (Fintype.card V - 1) := by
  exact is_tree_card_coloring_three_aux (Fintype.card V) V T rfl hT
