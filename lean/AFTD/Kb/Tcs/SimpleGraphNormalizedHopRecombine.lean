import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHop
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_normalized_hop_recombine

Topic: graphs   Node: c10424ceb7de

Provenance: helper lemma. Uniform structural helper for IN-262 / OP-543, using the hop and leap-group definitions of arXiv:2610.18463. The universal quadratic word bound is a question proposed here, not a theorem of that paper. No diameter estimate or research advance is claimed by this algebraic normalization.

If p is allowed relative to a baseline hop h0, and a PERMUTATION q chooses p(v) or v at each vertex, then q is also allowed relative to h0. The bijectivity of q remains an explicit hypothesis in its type.
-/

theorem simple_graph_normalized_hop_recombine {V : Type*} (G : SimpleGraph V)
    (h₀ p q : Equiv.Perm V) (hh₀ : simple_graph_is_hop G h₀)
    (hp : simple_graph_normalized_hop G h₀ p)
    (hq : ∀ v, q v = p v ∨ q v = v) :
    simple_graph_normalized_hop G h₀ q := by
  intro v
  change G.Adj v (h₀ (q v))
  rcases hq v with he | he
  · rw [he]
    exact hp v
  · rw [he]
    exact hh₀ v
