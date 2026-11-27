import AFTD.Prelude
import AFTD.Kb.Tcs.ForcedMatchingEdgeExcludesAdjacentTrueTwin
import AFTD.Kb.Tcs.PerfectMatchingForcedEdgeInEveryMatching

/-!
# op1957_saturated_forced_residual_single_block_vertex

Topic: graphs   Node: 25f663ad2a8f

Provenance: helper lemma. OP-1957: saturated-block boundary reduction, arXiv:2611.22690 and arXiv:1011.3384

In the displayed four-block graph with fully saturated A, a perfect-matchable residual in which an A-to-C edge is forced meets A only at its endpoint.
-/

theorem op1957_saturated_forced_residual_single_block_vertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D R : Finset V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hsat : ∀ a ∈ A, ∀ w ∈ A ∪ C ∪ D, a ≠ w → G.Adj a w)
    (x y : V) (hxA : x ∈ A) (hyC : y ∈ C) (hxR : x ∈ R) (hyR : y ∈ R)
    (hP : ∃ P : (G.induce {v | v ∈ R}).Subgraph, P.IsPerfectMatching)
    (hforced : ¬ ∃ P : ((G.induce {v | v ∈ R}).deleteEdges {s(⟨x,hxR⟩,⟨y,hyR⟩)}).Subgraph, P.IsPerfectMatching) :
    A ∩ R = {x} := by
  classical
  let H := G.induce {v | v ∈ R}
  let x' : {v // v ∈ R} := ⟨x,hxR⟩
  let y' : {v // v ∈ R} := ⟨y,hyR⟩
  obtain ⟨P,hP⟩ := hP
  have hxyP : P.Adj x' y' := perfect_matching_forced_edge_in_every_matching H x' y' hforced P hP
  have hforce : ∀ Q : H.Subgraph, Q.IsPerfectMatching → Q.Adj x' y' := by
    intro Q hQ
    exact perfect_matching_forced_edge_in_every_matching H x' y' hforced Q hQ
  have hout : ∀ a ∈ A, a ≠ x → a ∉ R := by
    intro a ha hax haR
    let a' : {v // v ∈ R} := ⟨a,haR⟩
    have hay : a ≠ y := fun h => Finset.disjoint_left.mp hAC ha (h ▸ hyC)
    have hxa : G.Adj x a := hsat x hxA a (Finset.mem_union_left _ (Finset.mem_union_left _ ha)) hax.symm
    have htwin : ∀ z, z ≠ x → z ≠ a → (G.Adj x z ↔ G.Adj a z) := by
      intro z hzx hza
      by_cases hzB : z ∈ B
      · have hxn := hnoAB x hxA z hzB
        have han := hnoAB a ha z hzB
        simp [hxn,han]
      · have hz : z ∈ A ∪ C ∪ D := by
          have hzall : z ∈ A ∪ B ∪ C ∪ D := by rw [hcover]; simp
          simp only [Finset.mem_union] at hzall ⊢
          rcases hzall with ((hzA | hzB') | hzC) | hzD
          · exact Or.inl (Or.inl hzA)
          · exact False.elim (hzB hzB')
          · exact Or.inl (Or.inr hzC)
          · exact Or.inr hzD
        have h1 := hsat x hxA z hz hzx.symm
        have h2 := hsat a ha z hz hza.symm
        simp [h1,h2]
    have htwin' : ∀ z : {v // v ∈ R}, z ≠ x' → z ≠ a' → (H.Adj x' z ↔ H.Adj a' z) := by
      intro z hzx hza
      have hzx' : z.val ≠ x := fun h => hzx (Subtype.ext h)
      have hza' : z.val ≠ a := fun h => hza (Subtype.ext h)
      exact htwin z.val hzx' hza'
    have hax' : a' ≠ x' := fun h => hax (congrArg Subtype.val h)
    have hay' : a' ≠ y' := fun h => hay (congrArg Subtype.val h)
    exact forced_matching_edge_excludes_adjacent_true_twin H P hP x' y' a' hxyP hax' hay' hxa htwin' hforce
  ext a
  constructor
  · intro ha
    obtain ⟨haA,haR⟩ := Finset.mem_inter.mp ha
    by_cases hax : a=x
    · simp [hax]
    · exact False.elim (hout a haA hax haR)
  · intro ha
    have ha' := Finset.mem_singleton.mp ha
    subst a
    exact Finset.mem_inter.mpr ⟨hxA,hxR⟩
