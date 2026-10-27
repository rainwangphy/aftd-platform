import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHop
import AFTD.Kb.Tcs.SimpleGraphIsHop
import AFTD.Kb.Tcs.SimpleGraphIsHopInv

/-!
# simple_graph_normalized_hop_two_word

Topic: graphs   Node: 0b33f0dd2c18

Provenance: helper lemma. Uniform structural helper for IN-262 / OP-543, using the hop and leap-group definitions of arXiv:2610.18463. The universal quadratic word bound is a question proposed here, not a theorem of that paper. No diameter estimate or research advance is claimed by this algebraic normalization.

Every normalized allowed permutation is the product of exactly two actual hops on an undirected graph. No vertex is allowed to wait during either actual hop.
-/

theorem simple_graph_normalized_hop_two_word {V : Type*} (G : SimpleGraph V)
    (h₀ p : Equiv.Perm V) (hh₀ : simple_graph_is_hop G h₀)
    (hp : simple_graph_normalized_hop G h₀ p) :
    ∃ w : List (Equiv.Perm V), (∀ h ∈ w, simple_graph_is_hop G h) ∧
      w.length = 2 ∧ w.prod = p := by
  refine ⟨[h₀⁻¹,h₀*p], ?_, by simp, by simp⟩
  intro h hh
  have hcases : h = h₀⁻¹ ∨ h = h₀*p := by simpa using hh
  rcases hcases with rfl | rfl
  · exact simple_graph_is_hop_inv G h₀ hh₀
  · exact hp
