import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable

/-!
# extendible_matching_residual_has_perfect_matching

Topic: graphs   Node: d42a7517f385

Provenance: helper lemma. Matching residual in OP-1957; https://arxiv.org/abs/2611.22690.

In a k-extendible graph, the vertices uncovered by a k-matching have a perfect matching.
-/

theorem extendible_matching_residual_has_perfect_matching
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ)
    (hext : is_k_extendable G k) (M : G.Subgraph)
    (hM : M.IsMatching) (hcard : M.edgeSet.ncard = k) :
    ∃ P : (G.induce {v | v ∉ M.verts}).Subgraph, P.IsPerfectMatching := by
  classical
  obtain ⟨P,hP,hMP⟩ := hext.2.2 M hM hcard
  have hcl : ∀ a b, P.Adj a b → a ∉ M.verts → b ∉ M.verts := by
    intro a b hab ha hbM
    obtain ⟨c,hc,_⟩ := hM hbM
    have hPc : P.Adj b c := hMP.2 hc
    have hca : c = a := (hP.1 (hP.2 b)).unique hPc hab.symm
    exact ha (hca ▸ M.edge_vert hc.symm)
  let f : (G.induce {v | v ∉ M.verts}) →g G := ⟨Subtype.val, by intro a b h; exact h⟩
  let P' := P.comap f
  refine ⟨P',?_⟩
  constructor
  · intro a ha
    obtain ⟨b,hab,huniq⟩ := hP.1 (hP.2 a.val)
    have hbR : b ∉ M.verts := hcl _ _ hab a.property
    refine ⟨⟨b,hbR⟩,⟨P.adj_sub hab,hab⟩,?_⟩
    intro c hc
    apply Subtype.ext
    exact huniq c.val hc.2
  · intro a
    exact hP.2 a.val
