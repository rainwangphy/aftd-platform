import AFTD.Prelude
import AFTD.Kb.Tcs.GStableKneser

/-!
# g_stable_kneser_adj

Topic: graphs   Node: 42cc9dfbc989

Provenance: helper lemma. scout/2610-17884-the-chromatic-number-of-g-stable-kneser-graphs.md:108

Two independent k-sets s and t in the G-stable Kneser graph KG(G, k) are adjacent if and only if their underlying vertex sets are disjoint and distinct.
-/

/-- Adjacency in the G-stable Kneser graph is given by disjointness and inequality of the independent sets. -/
theorem g_stable_kneser_adj {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (s t : { s : Finset V // G.IsNIndepSet k s }) :
    (GStableKneser G k).Adj s t ↔ Disjoint s.1 t.1 ∧ s ≠ t := by
  rfl
