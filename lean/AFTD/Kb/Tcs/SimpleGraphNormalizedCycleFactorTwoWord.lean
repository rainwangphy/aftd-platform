import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopRecombine
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopTwoWord
import AFTD.Kb.Tcs.SimpleGraphIsHop
import AFTD.Kb.Tcs.SimpleGraphNormalizedHop

/-!
# simple_graph_normalized_cycle_factor_two_word

Topic: graphs   Node: eecc248f5852

Provenance: helper lemma. Routine word-metric/cycle-factor assembly for IN-262 / OP-543, using the verified baseline normalization. The remaining quadratic diameter theorem is conjectural; no diameter assumption is silently discharged and no research advance is claimed.

Every individual disjoint cycle factor of a normalized allowed permutation can be isolated as a product of two actual hops. The intermediate baseline moves all vertices, so this does not assume idle moves in the original graph.
-/

theorem simple_graph_normalized_cycle_factor_two_word {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h₀ p q : Equiv.Perm V) (hh₀ : simple_graph_is_hop G h₀)
    (hp : simple_graph_normalized_hop G h₀ p) (hq : q ∈ p.cycleFactorsFinset) :
    ∃ w : List (Equiv.Perm V), (∀ h ∈ w, simple_graph_is_hop G h) ∧
      w.length = 2 ∧ w.prod = q := by
  have hq_agree : ∀ v : V, q v = p v ∨ q v = v := by
    intro v
    by_cases hv : v ∈ q.support
    · left
      exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hq).2 v hv
    · right
      exact Equiv.Perm.notMem_support.mp hv
  have hq_norm : simple_graph_normalized_hop G h₀ q :=
    simple_graph_normalized_hop_recombine G h₀ p q hh₀ hp hq_agree
  exact simple_graph_normalized_hop_two_word G h₀ q hh₀ hq_norm
