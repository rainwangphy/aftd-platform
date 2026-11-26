import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphExpansion
import AFTD.Kb.Tcs.DigraphClosedOutNbr

/-!
# digraph_expansion_submodular

Topic: graphs   Node: 93f65e0636c5

Provenance: formalization of a published result. Source: scout/2611-32872-a-short-proof-of-seymour-s-second-neighborhood-conjecture.md:238

For a finite type V with decidable equality, a directed graph G on V with decidable adjacency relation, and any two finite vertex sets X and Y, the expansion function digraph_expansion G is submodular: digraph_expansion G (X ∩ Y) + digraph_expansion G (X ∪ Y) ≤ digraph_expansion G X + digraph_expansion G Y.
-/

private lemma digraph_expansion_submodular_subset_closed_out_nbr {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (S : Finset V) :
    S ⊆ digraph_closed_out_nbr G S := by
  intro z hz
  simp only [digraph_closed_out_nbr, Finset.mem_union]
  exact Or.inl hz

private lemma digraph_expansion_submodular_closed_out_nbr_union {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    digraph_closed_out_nbr G (X ∪ Y) = digraph_closed_out_nbr G X ∪ digraph_closed_out_nbr G Y := by
  ext z
  simp only [digraph_closed_out_nbr, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and]
  aesop

private lemma digraph_expansion_submodular_closed_out_nbr_inter {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    digraph_closed_out_nbr G (X ∩ Y) ⊆ digraph_closed_out_nbr G X ∩ digraph_closed_out_nbr G Y := by
  intro z hz
  simp only [digraph_closed_out_nbr, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_inter] at hz ⊢
  aesop

/-- The out-boundary expansion function b on vertex finsets of a directed graph is submodular. -/
theorem digraph_expansion_submodular {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    digraph_expansion G (X ∩ Y) + digraph_expansion G (X ∪ Y) ≤
      digraph_expansion G X + digraph_expansion G Y := by
  have hexp : ∀ S : Finset V, digraph_expansion G S = (digraph_closed_out_nbr G S).card - S.card := by
    intro S
    simp only [digraph_expansion, digraph_out_boundary]
    exact Finset.card_sdiff_of_subset (digraph_expansion_submodular_subset_closed_out_nbr G S)
  rw [hexp, hexp, hexp, hexp]
  have hunion := digraph_expansion_submodular_closed_out_nbr_union G X Y
  have hint := digraph_expansion_submodular_closed_out_nbr_inter G X Y
  have hX : X.card ≤ (digraph_closed_out_nbr G X).card :=
    Finset.card_le_card (digraph_expansion_submodular_subset_closed_out_nbr G X)
  have hY : Y.card ≤ (digraph_closed_out_nbr G Y).card :=
    Finset.card_le_card (digraph_expansion_submodular_subset_closed_out_nbr G Y)
  have hXY : (X ∩ Y).card ≤ (digraph_closed_out_nbr G (X ∩ Y)).card :=
    Finset.card_le_card (digraph_expansion_submodular_subset_closed_out_nbr G (X ∩ Y))
  have hXUY : (X ∪ Y).card ≤ (digraph_closed_out_nbr G (X ∪ Y)).card :=
    Finset.card_le_card (digraph_expansion_submodular_subset_closed_out_nbr G (X ∪ Y))
  have hcardunion : (digraph_closed_out_nbr G X ∪ digraph_closed_out_nbr G Y).card
      + (digraph_closed_out_nbr G X ∩ digraph_closed_out_nbr G Y).card
      = (digraph_closed_out_nbr G X).card + (digraph_closed_out_nbr G Y).card :=
    Finset.card_union_add_card_inter _ _
  have hintercard : (digraph_closed_out_nbr G (X ∩ Y)).card ≤
      (digraph_closed_out_nbr G X ∩ digraph_closed_out_nbr G Y).card :=
    Finset.card_le_card hint
  have hxycard : (X ∪ Y).card + (X ∩ Y).card = X.card + Y.card := by
    have := Finset.card_union_add_card_inter X Y
    omega
  rw [hunion] at *
  omega
