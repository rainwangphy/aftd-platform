import AFTD.Prelude

/-!
# GStableKneser

Topic: graphs   Node: fdadfecbb55a

Provenance: formalization of a published result. Source: scout/2610-17884-the-chromatic-number-of-g-stable-kneser-graphs.md:108

For a simple graph G and a natural number k, the G-stable Kneser graph KG(G, k) is the simple graph whose vertices are the independent subsets of vertices of G of cardinality k, with an edge between two such sets if and only if they are disjoint and distinct.
-/

/-- The G-stable Kneser graph KG(G, k), whose vertices are the independent k-sets of G and whose edges join disjoint independent sets. -/
def GStableKneser {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph { s : Finset V // G.IsNIndepSet k s } where
  Adj s t := Disjoint s.1 t.1 ∧ s ≠ t
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩
