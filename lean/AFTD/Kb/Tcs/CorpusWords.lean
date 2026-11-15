import AFTD.Prelude

/-!
# corpus_words

Topic: approximation   Node: 3ce688d4cb55

Provenance: formalization of a published result. Source: arXiv:2611.15074 Reduction 1 (VC to FAC)

Given a finite type V with decidable equality and a simple graph G on V with decidable adjacency, corpus_words G is the Finset of lists over the alphabet V ⊕ (G.edgeSet × Fin 3) formed by taking the union over all edges e in G.edgeFinset of the four words [u, c, v], [u, c, r], [l, c, v], and [l, c, r], where (u, v) = Quot.out e gives the chosen orientation of the endpoints of e, and c = (e, 0), l = (e, 1), r = (e, 2) in G.edgeSet × Fin 3.
-/

/-- The reduction corpus X_G consisting of 4 words per edge of G over the alphabet V ⊕ (G.edgeSet × Fin 3). -/
noncomputable def corpus_words {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (List (V ⊕ (G.edgeSet × Fin 3))) :=
  G.edgeFinset.attach.biUnion (fun ⟨e, he⟩ =>
    let u : V ⊕ (G.edgeSet × Fin 3) := Sum.inl (Quot.out e).1
    let v : V ⊕ (G.edgeSet × Fin 3) := Sum.inl (Quot.out e).2
    let c : V ⊕ (G.edgeSet × Fin 3) := Sum.inr (⟨e, SimpleGraph.mem_edgeFinset.mp he⟩, 0)
    let l : V ⊕ (G.edgeSet × Fin 3) := Sum.inr (⟨e, SimpleGraph.mem_edgeFinset.mp he⟩, 1)
    let r : V ⊕ (G.edgeSet × Fin 3) := Sum.inr (⟨e, SimpleGraph.mem_edgeFinset.mp he⟩, 2)
    {[u, c, v], [u, c, r], [l, c, v], [l, c, r]})
