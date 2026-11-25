import AFTD.Prelude
import AFTD.Kb.Tcs.IsTypeIiEdge
import AFTD.Kb.Tcs.IsGoodSetForEdge

/-!
# type_ii_edge_two_neighbourhoods_eq

Topic: graphs   Node: 061edeb67da4

Provenance: helper lemma. step towards claw_free_minimal_bicritical_no_type_ii_edge

If uv is a type II edge with parameter 2 in a finite simple graph G and both u and v have degree at least 4, then u and v have the same neighbourhood: there is a 3-element set S, disjoint from {u, v}, with N(u) = {v} ∪ S and N(v) = {u} ∪ S.
-/

/-- A type II edge between vertices of degree at least 4 makes them adjacent twins: N(u) = {v} ∪ S and N(v) = {u} ∪ S with |S| = 3. -/
theorem type_ii_edge_two_neighbourhoods_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (hu : 4 ≤ G.degree u) (hv : 4 ≤ G.degree v) (h : is_type_ii_edge G u v 2) :
    ∃ S : Finset V, S.card = 3 ∧ u ∉ S ∧ v ∉ S ∧
      (∀ w : V, G.Adj u w ↔ w = v ∨ w ∈ S) ∧
      (∀ w : V, G.Adj v w ↔ w = u ∨ w ∈ S) := by
  obtain ⟨huv, ⟨S, hSg, hScard⟩, hmin, hlast⟩ := h
  have hScard3 : S.card = 3 := by simpa using hScard
  obtain ⟨huS, hvS, hcomp, hsupp1, hsupp2⟩ := hlast S hSg hScard3
  let H := SimpleGraph.induce (↑S)ᶜ (G.deleteEdges {s(u, v)})
  have hsupp1' : (H.connectedComponentMk ⟨u, huS⟩).supp = {⟨u, huS⟩} := hsupp1
  have hsupp2' : (H.connectedComponentMk ⟨v, hvS⟩).supp = {⟨v, hvS⟩} := hsupp2
  -- If x is one endpoint of uv and its component in (G - uv)[Sᶜ] is the singleton {x},
  -- then every neighbour of x is the other endpoint or lies in S.
  have key : ∀ (x y : V) (hxy : G.Adj x y) (hxy' : s(x, y) = s(u, v))
      (hxS : x ∉ S) (hyS : y ∉ S),
      (H.connectedComponentMk ⟨x, hxS⟩).supp = {⟨x, hxS⟩} →
      ∀ w, G.Adj x w → w = y ∨ w ∈ S := by
    intro x y hxy hxy' hxS hyS hsupp w hxw
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hwy, hwS⟩ := hcon
    have hne : s(x, w) ≠ s(u, v) := by
      intro heq
      have h2 : s(x, w) = s(x, y) := by rw [heq, hxy']
      rcases Sym2.eq_iff.mp h2 with ⟨-, h'⟩ | ⟨h', -⟩
      · exact hwy h'
      · exact hxy.ne h'
    have hadj : H.Adj ⟨x, hxS⟩ ⟨w, hwS⟩ := by
      simp only [H, SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
      exact ⟨hxw, hne⟩
    have hreach : H.Reachable ⟨x, hxS⟩ ⟨w, hwS⟩ := hadj.reachable
    have hcomp_eq : H.connectedComponentMk ⟨x, hxS⟩ = H.connectedComponentMk ⟨w, hwS⟩ :=
      SimpleGraph.ConnectedComponent.sound hreach
    have hmem : ⟨w, hwS⟩ ∈ (H.connectedComponentMk ⟨x, hxS⟩).supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact hcomp_eq.symm
    rw [hsupp, Set.mem_singleton_iff] at hmem
    have hwx : w = x := congrArg Subtype.val hmem
    exact hxw.ne hwx.symm
  have key_u := key u v huv rfl huS hvS hsupp1'
  have key_v := key v u huv.symm Sym2.eq_swap hvS huS hsupp2'
  -- Since uv is type II with parameter 2, both degrees are exactly 4, and the
  -- neighbourhoods are contained in {other endpoint} ∪ S, giving equality.
  have count : ∀ (x y : V) (hxy : G.Adj x y) (hx : x = u ∨ x = v) (hxS : x ∉ S)
      (hyS : y ∉ S), (∀ w, G.Adj x w → w = y ∨ w ∈ S) → ∀ w, w ∈ S → G.Adj x w := by
    intro x y hxy hx hxS hyS hkey w hwS
    have hcont : G.neighborFinset x ⊆ insert y S := by
      intro z hz
      rw [SimpleGraph.mem_neighborFinset] at hz
      rcases hkey z hz with rfl | hzS
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem hzS
    have hcard_insert : (insert y S).card = 4 := by
      rw [Finset.card_insert_of_notMem hyS, hScard3]
    have hcard_nb : (G.neighborFinset x).card = G.degree x :=
      SimpleGraph.card_neighborFinset_eq_degree G x
    have hdeg : G.degree x ≤ 4 := by
      calc G.degree x = (G.neighborFinset x).card := hcard_nb.symm
        _ ≤ (insert y S).card := Finset.card_le_card hcont
        _ = 4 := hcard_insert
    have hge : 4 ≤ G.degree x := by
      rcases hx with rfl | rfl
      · exact hu
      · exact hv
    have hdeg4 : G.degree x = 4 := le_antisymm hdeg hge
    have heq : G.neighborFinset x = insert y S := by
      apply Finset.eq_of_subset_of_card_le hcont
      rw [hcard_insert, hcard_nb, hdeg4]
    have : w ∈ G.neighborFinset x := by
      rw [heq]; exact Finset.mem_insert_of_mem hwS
    rwa [SimpleGraph.mem_neighborFinset] at this
  have cu := count u v huv (Or.inl rfl) huS hvS key_u
  have cv := count v u huv.symm (Or.inr rfl) hvS huS key_v
  refine ⟨S, hScard3, huS, hvS, ?_, ?_⟩
  · intro w
    constructor
    · exact key_u w
    · rintro (rfl | hwS)
      · exact huv
      · exact cu w hwS
  · intro w
    constructor
    · exact key_v w
    · rintro (rfl | hwS)
      · exact huv.symm
      · exact cv w hwS
