import AFTD.Prelude
import AFTD.Kb.Tcs.IsSustainableTree
import AFTD.Kb.Tcs.IsTreeIffIsAcyclicAndCard
import AFTD.Kb.Tcs.IsSustainableEdge
import AFTD.Kb.Tcs.AdjacencySpectralRadius

/-!
# no_sustainable_tree_fin_two

Topic: graphs   Node: 6ef3d787e400

Provenance: helper lemma. step towards op223_poset_connectivity

No simple graph on the two-element vertex type Fin 2 is a sustainable tree: a tree there has one edge and the complement has no edge at all, so no edge of it can be sustained by a swap.
-/

/-- On Fin 2 the unique tree (a single edge) has empty complement edge set, hence is not sustainable; this makes the sustainable half of op223_poset_connectivity vacuous at n = 2. -/
theorem no_sustainable_tree_fin_two (X : SimpleGraph (Fin 2)) : ¬ is_sustainable_tree X := by
  rintro ⟨hTree, hsus⟩
  -- A tree on Fin 2 has exactly one edge.
  have hcard : Nat.card X.edgeSet + 1 = Nat.card (Fin 2) :=
    (is_tree_iff_is_acyclic_and_card X).mp hTree |>.2
  have h2 : Nat.card (Fin 2) = 2 := by simp
  have hpos : 0 < Nat.card X.edgeSet := by omega
  obtain ⟨⟨e, he⟩, -⟩ := Nat.card_ne_zero.mp hpos.ne'
  obtain ⟨f, hf, -⟩ := (hsus e he).2
  -- On Fin 2 any two distinct vertices span the same single unordered pair, so all
  -- adjacencies between distinct vertices are equivalent to `X.Adj 0 1`.
  have hkey : ∀ a b : Fin 2, a ≠ b → (X.Adj a b ↔ X.Adj 0 1) := by
    intro a b hab
    have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Iff.rfl
    · rw [SimpleGraph.adj_comm]
    · exact absurd rfl hab
  revert he hf
  induction e using Sym2.ind with
  | h a b =>
    induction f using Sym2.ind with
    | h c d =>
      intro he hf
      rw [SimpleGraph.mem_edgeSet] at he hf
      have hab : a ≠ b := X.ne_of_adj he
      have hcd : c ≠ d := Xᶜ.ne_of_adj hf
      -- `X` is adjacent at `0,1`, while its complement is not.
      have h01 : X.Adj 0 1 := (hkey a b hab).mp he
      have hnc : ¬ X.Adj c d := ((SimpleGraph.compl_adj X c d).mp hf).2
      exact hnc ((hkey c d hcd).mpr h01)
