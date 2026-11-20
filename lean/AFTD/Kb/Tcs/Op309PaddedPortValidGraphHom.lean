import AFTD.Prelude
import AFTD.Kb.Tcs.Op309PaddedAlmostStarPortGraphValid
import AFTD.Kb.Tcs.Op309PaddedBoundaryPort

/-!
# op309_padded_port_valid_graph_hom

Topic: graphs   Node: 1d0891aae338

Provenance: helper lemma. OP-309 padded port-class selection, IN-1099.

Any graph homomorphism transports a valid padded port map to its codomain, preserving every required equality and local clique.
-/

theorem op309_padded_port_valid_graph_hom{V W W' : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset G.edgeSet) (Q : SimpleGraph W) (Q' : SimpleGraph W')
    (q : Sum G.edgeSet (V × Fin 3) → W) (f : Q →g Q')
    (h : op309_padded_almost_star_port_graph_valid G R Q q) :
    op309_padded_almost_star_port_graph_valid G R Q' (fun x => f (q x)) := by
  have hp : ∀ l : List W, l.Pairwise Q.Adj → (l.map f).Pairwise Q'.Adj := by
    intro l hl
    apply List.pairwise_map.mpr
    exact hl.imp (fun hab => f.map_rel hab)
  rcases h with ⟨hu, h3, h4, hs⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv e e' he he' hve hve' hne
    exact f.map_rel (hu v hv e e' he he' hve hve' hne)
  · intro a b c hn hab hbc ha hb hc ea ea' eb ec ec' hea hea' hne heb hec hec' hne'
    obtain ⟨hEq, hclique⟩ := h3 a b c hn hab hbc ha hb hc ea ea' eb ec ec' hea hea' hne heb hec hec' hne'
    constructor
    · rcases hEq with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact Or.inl ⟨congrArg f h₁, congrArg f h₂⟩
      · exact Or.inr ⟨congrArg f h₁, congrArg f h₂⟩
    · simpa using hp [q eb, q ea, q ea'] hclique
  · intro a b c d hn hab hbc hcd ha hb hc hd ea ea' eb ec ed ed' hea hea' hne heb hec hed hed' hne'
    obtain ⟨x,y,hx,hy,hclique⟩ := h4 a b c d hn hab hbc hcd ha hb hc hd ea ea' eb ec ed ed' hea hea' hne heb hec hed hed' hne'
    refine ⟨x,y,?_,?_,?_⟩
    · simpa only [apply_ite] using congrArg f hx
    · simpa only [apply_ite] using congrArg f hy
    · simpa only [List.map_cons, List.map_nil, apply_ite] using
        hp [q eb, q ec, q (if x then ea' else ea), q (if y then ed' else ed)] hclique
  · intro x a b d hn hxa hxb hxd hx ha hb hd ea ea' eb eb' ed ed' hea hea' hne heb heb' hne' hed hed' hne''
    obtain ⟨h₁,h₂,h₃⟩ := hs x a b d hn hxa hxb hxd hx ha hb hd ea ea' eb eb' ed ed' hea hea' hne heb heb' hne' hed hed' hne''
    refine ⟨?_,?_,f.map_rel h₃⟩
    · rcases h₁ with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact Or.inl ⟨congrArg f h₁, congrArg f h₂⟩
      · exact Or.inr ⟨congrArg f h₁, congrArg f h₂⟩
    · rcases h₂ with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact Or.inl ⟨congrArg f h₁, congrArg f h₂⟩
      · exact Or.inr ⟨congrArg f h₁, congrArg f h₂⟩
