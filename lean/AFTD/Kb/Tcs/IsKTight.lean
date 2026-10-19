import AFTD.Prelude
import AFTD.Kb.Tcs.GStableKneser

/-!
# is_k_tight

Topic: graphs   Node: c3f06778cc7d

Provenance: formalization of a published result. Source: arXiv:2610.17884 Sec. 1 -- The chromatic number of G-stable Kneser graphs

A finite graph G on n vertices is k-tight if the chromatic number of its G-stable Kneser graph KG(G, k) equals n - 2*k + 2.
-/

/-- A finite graph G on n vertices is k-tight if the chromatic number of its G-stable Kneser graph is n - 2*k + 2. -/
def is_k_tight {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop := (GStableKneser G k).chromaticNumber = ((Fintype.card V - 2 * k + 2 : ℕ) : ℕ∞)
