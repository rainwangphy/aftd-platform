import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.Tcs.InducedPerfectMatchingNeighborsCardBound

/-!
# extendible_independent_anticomplete_matching_obstruction_general

Topic: graphs   Node: 746d77ab0f71

Provenance: helper lemma. OP-1957; matching-deficit reduction at arbitrary finite order.

In a finite k-extendible graph, an independent set U and a disjoint anticomplete set W with 2|U|+|W| greater than the unmatched vertex count meet every matchable 2k-vertex set.
-/

set_option maxHeartbeats 2000000

theorem extendible_independent_anticomplete_matching_obstruction_general
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ)
    (hext : is_k_extendable G k)
    (U W S : Finset V) (hUW : Disjoint U W)
    (hind : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v)
    (hanti : ∀ u ∈ U, ∀ v ∈ W, ¬ G.Adj u v)
    (hS : Disjoint S (U ∪ W)) (hScard : S.card=2*k)
    (hlarge : Fintype.card V-2*k < 2*U.card+W.card) :
    ¬ (∃ M : (G.induce {v | v ∈ S}).Subgraph, M.IsPerfectMatching) := by
  classical
  intro hmatch
  let R : Finset V := Finset.univ \ S
  have hR : {v : V | v ∈ R} = ({v : V | v ∈ S})ᶜ := by
    ext v
    simp [R]
  have hcardS : ({v : V | v ∈ S} : Set V).ncard = 2*k := by
    change (S : Set V).ncard = 2*k
    rw [Set.ncard_coe_finset]
    exact hScard
  have hmatchR := extendible_matchable_two_k_vertices_complement_matchable G k hext
    {v | v ∈ S} hcardS hmatch
  rw [← hR] at hmatchR
  have hsub : U ∪ W ⊆ R := by
    intro v hv
    have hnS : v ∉ S := fun hs => Finset.disjoint_left.mp hS hs hv
    simp [R,hnS]
  have hU : U ⊆ R := fun v hv => hsub (Finset.mem_union_left _ hv)
  have hcover : ∀ u ∈ U, ∀ v ∈ R, G.Adj u v → v ∈ R \ (U ∪ W) := by
    intro u hu v hv hadj
    refine Finset.mem_sdiff.mpr ⟨hv,?_⟩
    intro hvUW
    rcases Finset.mem_union.mp hvUW with hvU | hvW
    · exact hind u hu v hvU hadj
    · exact hanti u hu v hvW hadj
  have hbound := induced_perfect_matching_neighbors_card_bound G R U (R \ (U ∪ W)) hU hcover hmatchR
  have hRcard : R.card = Fintype.card V-2*k := by
    have hh := Finset.card_sdiff_add_card_inter (Finset.univ : Finset V) S
    simp only [Finset.univ_inter,Finset.card_univ,hScard] at hh
    dsimp [R]
    have hextsize := hext.1
    omega
  have hh := Finset.card_sdiff_add_card_inter R (U ∪ W)
  have hi : R ∩ (U ∪ W) = U ∪ W := Finset.inter_eq_right.mpr hsub
  rw [hi,Finset.card_union_of_disjoint hUW,hRcard] at hh
  omega
